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

use std::cell::Cell;

use hash_ast::ast::*;
use hash_reporting::diagnostic::AccessToDiagnostics;
use hash_source::{
    location::{ByteRange, Span},
    Source,
};
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

/// Macro that allow for a flag within the [AstGen] logic to
/// be enabled in the current scope and then disabled after the
/// statement has finished executing.
///
/// Warning: If the inner `statement` has a exit-early language
/// constructor such as the `?` operator, then the flag will then
/// not be disabled. It is clear to see that in some situations this
/// might not be desirable and therefore some custom logic should be
/// implemented to revert the flag value even on failure.
#[macro_export]
macro_rules! enable_flag {
    ($gen: ident; $flag: ident; $statement: stmt) => {
        let value = $gen.$flag.get();

        $gen.$flag.set(true);
        $statement
        $gen.$flag.set(value);
    };
}

/// Macro that allow for a flag within the [AstGen] logic to
/// be disabled in the current scope and then reverted after the
/// statement finishes executing.
///
/// Warning: If the inner `statement` has a exit-early language
/// constructor such as the `?` operator, then the flag will then
/// not be reverted. It is clear to see that in some situations this
/// might not be desirable and therefore some custom logic should be
/// implemented to revert the flag value even on failure.
#[macro_export]
macro_rules! disable_flag {
    ($gen: ident; $flag: ident; $statement: stmt) => {
        let value = $gen.$flag.get();

        $gen.$flag.set(false);
        $statement
        $gen.$flag.set(value);
    };
}

/// The [AstGen] struct it the primary parser for the Hash compiler. It
/// will take a token stream and its accompanying token trees and will
/// convert the stream into an AST.
pub struct AstGen<'stream, 'resolver> {
    /// Current token stream offset.
    offset: Cell<usize>,

    /// The span of the current generator, the root generator does not have a
    /// parent span, whereas as child generators might need to use the span
    /// to report errors if their token streams are empty (and they're
    /// expecting them to be non empty.) For example, if the expression
    /// `k[]` was being parsed, the index component `[]` is expected to be
    /// non-empty, so the error reporting can grab the span of the `[]` and
    /// report it as an expected expression.
    parent_span: ByteRange,

    source: Source<'stream>,

    /// The token stream
    stream: &'stream [Token],

    /// Token trees that were generated from the stream
    token_trees: &'stream [Vec<Token>],

    /// Instance of an [ImportResolver] to notify the parser of encountered
    /// imports.
    pub(crate) resolver: &'resolver ImportResolver<'resolver>,

    /// Collected diagnostics for the current [AstGen]
    pub(crate) diagnostics: &'stream ParserDiagnostics,
}

/// Implementation of the [AstGen] with accompanying functions to parse specific
/// language components.
impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Create new AST generator from a token stream.
    pub fn new(
        source: Source<'stream>,
        stream: &'stream [Token],
        token_trees: &'stream [Vec<Token>],
        resolver: &'resolver ImportResolver,
        diagnostics: &'stream ParserDiagnostics,
    ) -> Self {
        // We compute the `parent_span` from the given strem.
        // If the stream has no tokens, then we assume that the
        // byte range is empty.
        let parent_span = match (stream.first(), stream.last()) {
            (Some(first), Some(last)) => first.span.join(last.span),
            _ => ByteRange::default(),
        };

        Self {
            source,
            stream,
            token_trees,
            offset: Cell::new(0),
            parent_span,
            resolver,
            diagnostics,
        }
    }

    /// Create new AST generator from a provided token stream with inherited
    /// module resolver and a provided parent span.
    #[must_use]
    pub fn from_stream(&self, stream: &'stream [Token], parent_span: ByteRange) -> Self {
        Self {
            source: self.source,
            stream,
            token_trees: self.token_trees,
            offset: Cell::new(0),
            parent_span,
            resolver: self.resolver,
            diagnostics: self.diagnostics,
        }
    }

    /// Get the [Span] of the current generator, this asserts that a parent
    /// [Span] is present.
    pub(crate) fn span(&self) -> Span {
        Span { range: self.parent_span, id: self.resolver.source() }
    }

    /// Function to create a [Span] from a [ByteRange] by using the
    /// provided resolver
    pub(crate) fn make_span(&self, range: ByteRange) -> Span {
        Span { range, id: self.resolver.source() }
    }

    /// Get the current offset of where the stream is at.
    #[inline(always)]
    pub(crate) fn offset(&self) -> usize {
        self.offset.get()
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

    /// Function to check if the token stream has been exhausted based on the
    /// current offset in the generator.
    pub(crate) fn has_token(&self) -> bool {
        let length = self.stream.len();

        match length {
            0 => false,
            _ => self.offset.get() < self.stream.len(),
        }
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

    /// Get a [Token] at a specified location in the stream. Panics if the given
    /// stream  position is out of bounds.
    #[inline(always)]
    pub(crate) fn token_at(&self, offset: usize) -> &Token {
        self.stream.get(offset).unwrap()
    }

    /// Get the current location from the current token, if there is no token at
    /// the current offset, then the location of the last token is used.
    pub(crate) fn current_pos(&self) -> ByteRange {
        // check that the length of current generator is at least one...
        if self.stream.is_empty() {
            return self.parent_span;
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

    /// Create a new [AstNode] from the information provided by the [AstGen]
    #[inline(always)]
    pub fn node<T>(&self, inner: T) -> AstNode<T> {
        AstNode::new(inner, self.make_span(self.current_pos()))
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    #[inline(always)]
    pub fn node_with_span<T>(&self, inner: T, location: ByteRange) -> AstNode<T> {
        AstNode::new(inner, self.make_span(location))
    }

    /// Create a new [AstNode] with a span that ranges from the start
    /// [ByteRange] to join with the [ByteRange].
    #[inline(always)]
    pub(crate) fn node_with_joined_span<T>(&self, body: T, start: ByteRange) -> AstNode<T> {
        AstNode::new(body, self.make_span(start.join(self.current_pos())))
    }

    /// Create [AstNodes] with a span.
    pub(crate) fn nodes_with_span<T>(
        &self,
        nodes: ThinVec<AstNode<T>>,
        location: ByteRange,
    ) -> AstNodes<T> {
        AstNodes::new(nodes, self.make_span(location))
    }

    /// Create [AstNodes] with a span that ranges from the start [ByteRange] to
    /// the current [ByteRange].
    pub(crate) fn nodes_with_joined_span<T>(
        &self,
        nodes: ThinVec<AstNode<T>>,
        start: ByteRange,
    ) -> AstNodes<T> {
        AstNodes::new(nodes, self.make_span(start.join(self.current_pos())))
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
        self.offset.set(self.offset.get() + 1);
        self.err(ParseErrorKind::UnExpected, ExpectedItem::empty(), Some(self.current_token().kind))
    }

    /// This function `consumes` a generator into the patent [AstGen] whilst
    /// also merging all of the warnings and errors that the `consumed` [AstGen]
    /// produced. If the `consumed` [AstGen] produced no errors, then we
    /// check that the stream other the generator has been exhausted.
    #[inline]
    pub(crate) fn consume_gen(&mut self, mut other: AstGen<'stream, 'resolver>) {
        // Ensure that the generator token stream has been exhausted
        if !other.has_errors() && other.has_token() {
            other.maybe_add_error::<()>(other.expected_eof());
        }
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
        &self,
        mut parse_fn: impl FnMut(&Self) -> Result<T, E>,
    ) -> Option<T> {
        let start = self.offset();

        match parse_fn(self) {
            Ok(result) => Some(result),
            Err(_) => {
                self.offset.set(start);
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
                self.offset.set(start);
                None
            }
        }
    }

    /// Function to parse an arbitrary number of 'parsing functions' separated
    /// by a singular 'separator' closure. The function has a behaviour of
    /// allowing trailing separator. This will also parse the function until
    /// the end of the current generator, and therefore it is intended to be
    /// used with a nested generator.
    ///
    /// **Note**: Call `consume_gen()` in the passed generator in order to
    /// merge any generated errors, and to emit a possible `expected_eof` at
    /// the end if applicable.
    pub(crate) fn parse_nodes<T>(
        &mut self,
        mut item: impl FnMut(&mut Self) -> ParseResult<AstNode<T>>,
        mut separator: impl FnMut(&mut Self) -> ParseResult<()>,
    ) -> AstNodes<T> {
        let start = self.current_pos();
        let mut args = thin_vec![];

        // flag specifying if the parser has errored but is trying to recover
        // by parsing the next item
        let mut recovery = false;

        while self.has_token() {
            match item(self) {
                Ok(element) => {
                    args.push(element);
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

        self.nodes_with_joined_span(args, start)
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
        let mut args = thin_vec![];

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
                    args.push(element);
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

        self.nodes_with_joined_span(args, start)
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
    pub(crate) fn parse_delim_tree(
        &self,
        delimiter: Delimiter,
        error: Option<ParseErrorKind>,
    ) -> ParseResult<Self> {
        match self.peek() {
            Some(Token { kind: TokenKind::Tree(inner, tree_index), span })
                if *inner == delimiter =>
            {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index as usize).unwrap();
                Ok(self.from_stream(tree, *span))
            }
            token => self.err_with_location(
                error.unwrap_or(ParseErrorKind::UnExpected),
                ExpectedItem::from(delimiter),
                token.map(|tok| tok.kind),
                token.map_or_else(|| self.current_pos(), |tok| tok.span),
            )?,
        }
    }

    /// Parse a [Module] which is simply made of a list of statements.
    ///
    /// The function returns [None] if parsing failed, which means the caller
    /// should get all the diagnostics for the current session.
    pub(crate) fn parse_module(&mut self) -> AstNode<Module> {
        let start = self.current_pos();
        let mut contents = thin_vec![];
        let mut macros = AstNodes::new(thin_vec![], self.make_span(start));

        while self.has_token() {
            // Check if we have a `#!` which represents a top-level
            // macro invocation.
            match (self.peek(), self.peek_second()) {
                (
                    Some(Token { kind: TokenKind::Pound, .. }),
                    Some(Token { kind: TokenKind::Exclamation, .. }),
                ) => {
                    self.offset.set(self.offset.get() + 2);

                    match self.parse_module_marco_invocations() {
                        Ok(items) => macros.merge(items),
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

        self.node_with_joined_span(
            Module {
                contents: self.nodes_with_joined_span(contents, start),
                macros: self.make_macro_invocations(macros),
            },
            start,
        )
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
