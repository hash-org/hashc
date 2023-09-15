//! Hash Compiler parser. The parser will take a generated token stream
//! and its accompanying token trees and will convert the stream into
//! an AST.

mod block;
mod definitions;
mod expr;
mod lit;
mod macros;
mod name;
mod operator;
mod pat;
mod ty;

use std::{cell::Cell, ops::Deref};

use hash_ast::ast::*;
use hash_reporting::diagnostic::HasDiagnosticsMut;
use hash_source::location::{ByteRange, Span, SpannedSource};
use hash_token::{delimiter::Delimiter, Token, TokenKind};
use hash_utils::thin_vec::{thin_vec, ThinVec};

use crate::{
    diagnostics::{
        error::{ParseError, ParseErrorKind, ParseResult},
        expected::ExpectedItem,
        ParserDiagnostics,
    },
    import_resolver::ImportResolver,
};

pub(crate) struct AstGenFrame<'s> {
    /// The current offset of the token stream.
    offset: Cell<usize>,

    /// If an error occurred in this frame.
    pub(crate) error: Cell<bool>,

    /// The span of the current generator, the root generator does not have a
    /// parent span, whereas as child generators might need to use the span
    /// to report errors if their token streams are empty (and they're
    /// expecting them to be non empty.) For example, if the expression
    /// `k[]` was being parsed, the index component `[]` is expected to be
    /// non-empty, so the error reporting can grab the span of the `[]` and
    /// report it as an expected expression.
    span: ByteRange,

    /// The current token stream.
    stream: &'s [Token],
}

impl<'s> AstGenFrame<'s> {
    pub fn from_stream(stream: &'s [Token], span: ByteRange) -> Self {
        Self { offset: Cell::new(0), error: Cell::new(false), span, stream }
    }

    /// Skip `n` number of tokens.
    #[inline(always)]
    pub(crate) fn skip(&self, n: u8) {
        self.offset.set(self.offset.get() + n as usize);
    }

    /// Backtrack `n` number of tokens.
    #[inline(always)]
    pub(crate) fn backtrack(&self, n: usize) {
        self.offset.set(self.offset.get() - n);
    }

    /// Function to check if the token stream has been exhausted based on the
    /// current offset in the generator.
    #[inline]
    pub(crate) fn has_token(&self) -> bool {
        let length = self.stream.len();

        match length {
            0 => false,
            _ => self.offset.get() < self.stream.len(),
        }
    }

    /// Get the current offset of where the stream is at.
    #[inline(always)]
    pub(crate) fn offset(&self) -> usize {
        self.offset.get()
    }

    /// Get a reference to the token stream.
    #[inline(always)]
    pub(crate) fn stream(&self) -> &'s [Token] {
        self.stream
    }

    /// Function to peek at the nth token ahead of the current offset.
    #[inline(always)]
    pub(crate) fn peek_nth(&self, at: usize) -> Option<&Token> {
        self.stream.get(self.offset.get() + at)
    }

    /// Attempt to peek one step token ahead.
    pub(crate) fn peek(&self) -> Option<&Token> {
        self.peek_nth(0)
    }

    /// Peek two tokens ahead.
    pub(crate) fn peek_second(&self) -> Option<&Token> {
        self.peek_nth(1)
    }

    /// Function that skips the next token without explicitly looking up the
    /// token in the stream and avoiding the additional computation.
    #[inline(always)]
    pub(crate) fn skip_token(&self) {
        self.offset.update(|x| x + 1);
    }

    /// Function that increases the offset of the next token
    pub(crate) fn next_token(&self) -> Option<&Token> {
        let value = self.stream.get(self.offset.get());

        if value.is_some() {
            self.offset.update::<_>(|x| x + 1);
        }

        value
    }

    /// Get the current [Token] in the stream. Panics if the current offset has
    /// passed the size of the stream, e.g tring to get the current token
    /// after reaching the end of the stream.
    pub(crate) fn current_token(&self) -> &Token {
        let offset = if self.offset.get() > 0 { self.offset.get() - 1 } else { 0 };
        self.stream.get(offset).unwrap()
    }

    /// Get the current location from the current token, if there is no token at
    /// the current offset, then the location of the last token is used.
    pub(crate) fn current_pos(&self) -> ByteRange {
        // check that the length of current generator is at least one...
        if self.stream.is_empty() {
            return self.span;
        }

        let offset = if self.offset.get() > 0 { self.offset.get() - 1 } else { 0 };

        match self.stream.get(offset) {
            Some(token) => token.span,
            None => self.stream.last().unwrap().span,
        }
    }

    /// Get the next location of the token, if there is no token after, we use
    /// the next character offset to determine the location.
    pub(crate) fn next_pos(&self) -> ByteRange {
        match self.peek() {
            Some(token) => token.span,
            None => {
                let span = self.current_pos();
                ByteRange::new(span.end(), span.end() + 1)
            }
        }
    }

    /// Get the [ByteRange] of the [AstGen].
    pub(crate) fn range(&self) -> ByteRange {
        self.span
    }
}

/// The [AstGen] struct it the primary parser for the Hash compiler. It
/// will take a token stream and its accompanying token trees and will
/// convert the stream into an AST.
pub(crate) struct AstGen<'s> {
    /// The current frame.
    pub(crate) frame: AstGenFrame<'s>,

    /// The source that we are currently parsing.
    source: SpannedSource<'s>,

    /// Token trees that were generated from the stream.
    token_trees: &'s [Vec<Token>],

    /// Local [AstNodeId] allocator.
    span_map: &'s mut LocalSpanMap,

    /// For resolving and queueing discovered module imports.
    resolver: &'s ImportResolver<'s>,

    /// Collected diagnostics for the current [AstGen].
    pub(crate) diagnostics: &'s mut ParserDiagnostics,
}

impl<'s> Deref for AstGen<'s> {
    type Target = AstGenFrame<'s>;

    fn deref(&self) -> &Self::Target {
        &self.frame
    }
}

/// Implementation of the [AstGen] with accompanying functions to parse specific
/// language components.
impl<'s> AstGen<'s> {
    /// Create new AST generator from a token stream.
    pub fn new(
        source: SpannedSource<'s>,
        stream: &'s [Token],
        token_trees: &'s [Vec<Token>],
        resolver: &'s ImportResolver,
        diagnostics: &'s mut ParserDiagnostics,
        span_map: &'s mut LocalSpanMap,
    ) -> Self {
        // We compute the `parent_span` from the given stream.
        // If the stream has no tokens, then we assume that the
        // byte range is empty.
        let parent_span = match (stream.first(), stream.last()) {
            (Some(first), Some(last)) => first.span.join(last.span),
            _ => ByteRange::default(),
        };

        Self {
            source,
            token_trees,
            frame: AstGenFrame::from_stream(stream, parent_span),
            resolver,
            diagnostics,
            span_map,
        }
    }

    /// Get the [Span] of the current generator, this asserts that a parent
    /// [Span] is present.
    pub(crate) fn span(&self) -> Span {
        Span { range: self.range(), id: self.resolver.source() }
    }

    /// Create new AST generator from a provided token stream with inherited
    /// module resolver and a provided parent span.
    pub fn new_frame<T>(
        &mut self,
        stream: &'s [Token],
        parent_span: ByteRange,
        mut gen: impl FnMut(&mut Self) -> T,
    ) -> T {
        let new_frame = AstGenFrame::from_stream(stream, parent_span);
        let old_frame = std::mem::replace(&mut self.frame, new_frame);
        let result = gen(self);
        let child_frame = std::mem::replace(&mut self.frame, old_frame);

        // Ensure that the generator token stream has been exhausted
        if !child_frame.error.get() && child_frame.has_token() {
            self.maybe_add_error::<()>(self.expected_eof());
        }

        result
    }

    /// Function to create a [Span] from a [ByteRange] by using the
    /// provided resolver
    pub(crate) fn make_span(&self, range: ByteRange) -> Span {
        Span { range, id: self.resolver.source() }
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    #[inline(always)]
    pub fn node<T>(&mut self, inner: T) -> AstNode<T> {
        let id = self.span_map.add(self.current_pos());
        AstNode::with_id(inner, id)
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    #[inline(always)]
    pub fn node_with_span<T>(&mut self, inner: T, location: ByteRange) -> AstNode<T> {
        let id = self.span_map.add(location);
        AstNode::with_id(inner, id)
    }

    /// Create a new [AstNode] with a span that ranges from the start
    /// [ByteRange] to join with the [ByteRange].
    #[inline(always)]
    pub(crate) fn node_with_joined_span<T>(&mut self, body: T, start: ByteRange) -> AstNode<T> {
        let id = self.span_map.add(start.join(self.current_pos()));
        AstNode::with_id(body, id)
    }

    /// Create [AstNodes] with a span.
    pub(crate) fn nodes_with_span<T>(
        &mut self,
        nodes: ThinVec<AstNode<T>>,
        location: ByteRange,
    ) -> AstNodes<T> {
        let id = self.span_map.add(location);
        AstNodes::with_id(nodes, id)
    }

    /// Create [AstNodes] with a span that ranges from the start [ByteRange] to
    /// the current [ByteRange].
    pub(crate) fn nodes_with_joined_span<T>(
        &mut self,
        nodes: ThinVec<AstNode<T>>,
        start: ByteRange,
    ) -> AstNodes<T> {
        let id = self.span_map.add(start.join(self.current_pos()));
        AstNodes::with_id(nodes, id)
    }

    /// Create an error without wrapping it in an [Err] variant
    #[inline(always)]
    fn make_err(
        &self,
        kind: ParseErrorKind,
        expected: ExpectedItem,
        received: Option<TokenKind>,
        span: Option<ByteRange>,
    ) -> ParseError {
        ParseError::new(
            kind,
            self.make_span(span.unwrap_or_else(|| self.current_pos())),
            expected,
            received,
        )
    }

    /// Create an error at the current location.
    pub(crate) fn err<T>(
        &self,
        kind: ParseErrorKind,
        expected: ExpectedItem,
        received: Option<TokenKind>,
    ) -> ParseResult<T> {
        Err(self.make_err(kind, expected, received, None))
    }

    /// Create an error at the current location.
    pub(crate) fn err_with_location<T>(
        &self,
        kind: ParseErrorKind,
        expected: ExpectedItem,
        received: Option<TokenKind>,
        span: ByteRange,
    ) -> ParseResult<T> {
        Err(self.make_err(kind, expected, received, Some(span)))
    }

    /// Generate an error that represents that within the current [AstGen] the
    /// `end of file` state should be reached. This means that either in the
    /// root generator there are no more tokens or within a nested generator
    /// (such as if the generator is within a brackets) that it should now
    /// read no more tokens.
    pub(crate) fn expected_eof<T>(&self) -> ParseResult<T> {
        // move onto the next token
        self.skip_token();
        self.err(ParseErrorKind::UnExpected, ExpectedItem::empty(), Some(self.current_token().kind))
    }

    /// Generate an error representing that the current generator unexpectedly
    /// reached the end of input at this point.
    pub(crate) fn unexpected_eof<T>(&self) -> ParseResult<T> {
        self.err(ParseErrorKind::UnExpected, ExpectedItem::empty(), None)
    }

    /// Function to peek ahead and match some parsing function that returns a
    /// [Option<T>]. If The result is an error, the function wil reset the
    /// current offset of the token stream to where it was the function was
    /// peeked. This is essentially a convertor from a [ParseResult<T>]
    /// into an [Option<T>] with the side effect of resetting the parser state
    /// back to it's original settings.
    pub(crate) fn peek_resultant_fn<T, E>(
        &mut self,
        mut parse_fn: impl FnMut(&mut Self) -> Result<T, E>,
    ) -> Option<T> {
        let start = self.offset();

        match parse_fn(self) {
            Ok(result) => Some(result),
            Err(_) => {
                self.frame.offset.set(start);
                None
            }
        }
    }

    /// Function to peek ahead and match some parsing function that returns a
    /// [Option<T>]. If The result is an error, the function wil reset the
    /// current offset of the token stream to where it was the function was
    /// peeked. This is essentially a convertor from a [ParseResult<T>]
    /// into an [Option<T>] with the side effect of resetting the parser state
    /// back to it's original settings.
    pub(crate) fn peek_resultant_fn_mut<T, E>(
        &mut self,
        mut parse_fn: impl FnMut(&mut Self) -> Result<T, E>,
    ) -> Option<T> {
        let start = self.offset();

        match parse_fn(self) {
            Ok(result) => Some(result),
            Err(_) => {
                self.frame.offset.set(start);
                None
            }
        }
    }

    /// Record the [ByteRange] that a parse function `f` traversed during
    /// its execution. This is useful for tracking the span of a node that
    /// is generated from a parse function.
    #[inline]
    pub(crate) fn track_span<T, E>(
        &mut self,
        mut f: impl FnMut(&mut Self) -> Result<T, E>,
    ) -> Result<(T, ByteRange), E> {
        let start = self.current_pos();
        let result = f(self)?;
        let end = self.current_pos();

        Ok((result, start.join(end)))
    }

    /// Function to parse an arbitrary number of 'parsing functions' separated
    /// by a singular 'separator' closure. The function has a behaviour of
    /// allowing trailing separator. This will also parse the function until
    /// the end of the current generator, and therefore it is intended to be
    /// used with a nested generator.
    ///
    /// ##Note: Call `consume_gen()` in the passed generator in order to
    /// merge any generated errors, and to emit a possible `expected_eof` at
    /// the end if applicable.
    #[inline]
    pub(crate) fn parse_node_collection<T>(
        &mut self,
        mut item: impl FnMut(&mut Self) -> ParseResult<AstNode<T>>,
        mut separator: impl FnMut(&mut Self) -> ParseResult<()>,
    ) -> ThinVec<AstNode<T>> {
        let mut items = thin_vec![];

        // flag specifying if the parser has errored but is trying to recover
        // by parsing the next item
        let mut recovery = false;

        while self.has_token() {
            match item(self) {
                Ok(element) => {
                    items.push(element);
                }
                // Rather than immediately returning the error here, we will push it into
                // the current diagnostics store, and then break the loop. If we couldn't
                // previously parse the `separator`, then
                Err(err) => {
                    if !recovery {
                        self.add_error(err);
                    }
                    break;
                }
            }

            if self.has_token() {
                match separator(self) {
                    Ok(_) => {
                        // reset recovery since we're in the 'green zone' despite
                        // potentially erroring previously
                        recovery = false;
                    }
                    // if we couldn't parse a separator, then let's try to
                    // recover by resetting the loop and trying to parse
                    // `item` again... if that also errors then we bail
                    // completely
                    Err(err) => {
                        self.add_error(err);
                        recovery = true;
                    }
                }
            }
        }

        items
    }

    /// Function to parse an arbitrary number of 'parsing functions' separated
    /// by a singular 'separator' closure. This will just convert the result
    /// from [`Self::parse_node_collection`] into an [`AstNodes`].
    ///
    /// ##Note: call `consume_gen()` on the generator that is used after
    /// completing the parsing of the nodes.
    pub(crate) fn parse_nodes<T>(
        &mut self,
        item: impl FnMut(&mut Self) -> ParseResult<AstNode<T>>,
        separator: impl FnMut(&mut Self) -> ParseResult<()>,
    ) -> AstNodes<T> {
        let start = self.current_pos();
        let nodes = self.parse_node_collection(item, separator);
        self.nodes_with_joined_span(nodes, start)
    }

    /// This function behaves identically to [parse_separated_fn] except that it
    /// might encounter items that don't produce an AST node. In this case,
    /// the item closure will return `Ok(None)`. This is useful for parsing
    /// items that are not required to be present, but if they are present,
    /// they might be added into another AST node expect this `args` one
    /// that is generated. Additionally, this provides an index for the the
    /// `item` closure to keep track of how many items have already
    /// been parsed.
    pub(crate) fn parse_nodes_with_skips<T>(
        &mut self,
        mut item: impl FnMut(&mut Self, usize) -> ParseResult<Option<AstNode<T>>>,
        mut separator: impl FnMut(&mut Self) -> ParseResult<()>,
    ) -> AstNodes<T> {
        let start = self.current_pos();
        let mut items = thin_vec![];

        // flag specifying if the parser has errored but is trying to recover
        // by parsing the next item
        let mut recovery = false;

        // the current index of the item being parsed. this is passed
        // to the item in order for it to use the current index of the
        // item it is trying to parse.
        let mut index = 0;

        while self.has_token() {
            match item(self, index) {
                Ok(Some(element)) => {
                    items.push(element);
                    index += 1;
                }
                // In this case, we just continue parsing, and increase
                // the element.
                Ok(None) => {
                    index += 1;
                }
                // Rather than immediately returning the error here, we will push it into
                // the current diagnostics store, and then break the loop. If we couldn't
                // previously parse the `separator`, then
                Err(err) => {
                    if !recovery {
                        self.add_error(err);
                    }
                    break;
                }
            }

            if self.has_token() {
                match separator(self) {
                    Ok(_) => {
                        // reset recovery since we're in the 'green zone' despite
                        // potentially erroring previously
                        recovery = false;
                    }
                    // if we couldn't parse a separator, then let's try to
                    // recover by resetting the loop and trying to parse
                    // `item` again... if that also errors then we bail
                    // completely
                    Err(err) => {
                        self.add_error(err);
                        recovery = true;
                    }
                }
            }
        }

        self.nodes_with_joined_span(items, start)
    }

    /// Function to parse the next [Token] with the specified [TokenKind].
    pub(crate) fn parse_token(&self, atom: TokenKind) -> ParseResult<()> {
        match self.peek() {
            Some(token) if token.has_kind(atom) => {
                self.skip_token();
                Ok(())
            }
            token => self.err_with_location(
                ParseErrorKind::UnExpected,
                ExpectedItem::from(atom),
                token.map(|t| t.kind),
                token.map_or_else(|| self.next_pos(), |t| t.span),
            ),
        }
    }

    /// Function to parse a token atom optionally. If the appropriate token atom
    /// is present we advance the token count, if not then just return None
    pub(crate) fn parse_token_fast(&self, kind: TokenKind) -> Option<()> {
        match self.peek() {
            Some(token) if token.has_kind(kind) => {
                self.skip_token();
                Some(())
            }
            _ => None,
        }
    }

    /// Utility function to parse a brace tree as the next token, if a brace
    /// tree isn't present, then an error is generated.
    pub(crate) fn in_tree<T>(
        &mut self,
        delimiter: Delimiter,
        error: Option<ParseErrorKind>,
        gen: impl FnMut(&mut Self) -> ParseResult<T>,
    ) -> ParseResult<T> {
        match self.peek() {
            Some(Token { kind: TokenKind::Tree(inner, tree_index), span })
                if *inner == delimiter =>
            {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index as usize).unwrap();
                self.new_frame(tree, *span, gen)
            }
            token => self.err_with_location(
                error.unwrap_or(ParseErrorKind::UnExpected),
                ExpectedItem::from(delimiter),
                token.map(|tok| tok.kind),
                token.map_or_else(|| self.current_pos(), |tok| tok.span),
            ),
        }
    }

    /// Parse a [Module] which is simply made of a list of statements.
    ///
    /// The function returns [None] if parsing failed, which means the caller
    /// should get all the diagnostics for the current session.
    pub(crate) fn parse_module(&mut self) -> AstNode<Module> {
        let start = self.current_pos();
        let mut contents = thin_vec![];
        let mut macros = thin_vec![];

        while self.has_token() {
            // Check if we have a `#!` which represents a top-level
            // macro invocation.
            match (self.peek(), self.peek_second()) {
                (
                    Some(Token { kind: TokenKind::Pound, .. }),
                    Some(Token { kind: TokenKind::Exclamation, .. }),
                ) => {
                    self.frame.skip(2);

                    match self.parse_module_marco_invocations() {
                        Ok(items) => macros.extend(items),
                        Err(err) => {
                            self.add_error(err);
                            break;
                        }
                    }
                }
                _ => {
                    match self.parse_top_level_expr() {
                        Ok(Some((_, expr))) => contents.push(expr),
                        Ok(_) => continue,
                        Err(err) => {
                            // @@Future: attempt error recovery here...
                            self.add_error(err);
                            break;
                        }
                    }
                }
            }
        }

        let contents = self.nodes_with_joined_span(contents, start);
        // @@Hack: we put a nonsense span here, but it doesn't seem that
        // we can do much better or that it even matters since the
        // top-level span of the macros will never be queries...
        let nodes = self.nodes_with_joined_span(macros, start);
        let macros = self.make_macro_invocations(nodes);
        self.node_with_joined_span(Module { contents, macros }, start)
    }

    /// This function is used to exclusively parse a interactive block which
    /// follows similar rules to a an actual block. Interactive statements
    /// are like ghost blocks without the actual braces to begin with. It
    /// follows that there are an arbitrary number of statements, followed
    /// by an optional final expression which doesn't need to be completed
    /// by a comma.
    ///
    /// The function returns [None] if parsing failed, which means the caller
    /// should get all the diagnostics for the current session.
    pub(crate) fn parse_expr_from_interactive(&mut self) -> AstNode<BodyBlock> {
        let start = self.current_pos();

        let body = self.parse_body_block_inner();
        self.node_with_joined_span(body, start)
    }
}
