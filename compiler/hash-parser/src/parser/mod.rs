//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
mod block;
mod definitions;
mod expr;
mod lit;
mod name;
mod operator;
mod pat;
mod ty;

use std::cell::Cell;

use hash_ast::ast::*;
use hash_source::location::{SourceLocation, Span};
use hash_token::{delimiter::Delimiter, Token, TokenKind, TokenKindVector};

use crate::{
    diagnostics::{
        error::{ParseError, ParseErrorKind, ParseResult},
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
    parent_span: Option<Span>,

    /// The token stream
    stream: &'stream [Token],

    /// Token trees that were generated from the stream
    token_trees: &'stream [Vec<Token>],

    /// State set by expression parsers for parents to let them know if the
    /// parsed expression was made up of multiple expressions with
    /// precedence operators.
    is_compound_expr: Cell<bool>,

    /// Instance of an [ImportResolver] to notify the parser of encountered
    /// imports.
    resolver: &'resolver ImportResolver<'resolver>,

    /// Collected diagnostics for the current [AstGen]
    pub(crate) diagnostics: ParserDiagnostics,
}

/// Implementation of the [AstGen] with accompanying functions to parse specific
/// language components.
impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Create new AST generator from a token stream.
    pub fn new(
        stream: &'stream [Token],
        token_trees: &'stream [Vec<Token>],
        resolver: &'resolver ImportResolver,
    ) -> Self {
        Self {
            stream,
            token_trees,
            parent_span: None,
            is_compound_expr: Cell::new(false),
            offset: Cell::new(0),
            resolver,
            diagnostics: ParserDiagnostics::default(),
        }
    }

    /// Create new AST generator from a provided token stream with inherited
    /// module resolver and a provided parent span.
    #[must_use]
    pub fn from_stream(&self, stream: &'stream [Token], parent_span: Span) -> Self {
        Self {
            stream,
            token_trees: self.token_trees,
            offset: Cell::new(0),
            is_compound_expr: self.is_compound_expr.clone(),
            parent_span: Some(parent_span),
            resolver: self.resolver,
            diagnostics: ParserDiagnostics::default(),
        }
    }

    /// Function to create a [SourceLocation] from a [Span] by using the
    /// provided resolver
    pub(crate) fn source_location(&self, span: &Span) -> SourceLocation {
        SourceLocation { span: *span, source_id: self.resolver.current_source_id() }
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
    pub(crate) fn current_location(&self) -> Span {
        // check that the length of current generator is at least one...
        if self.stream.is_empty() {
            return self.parent_span.unwrap_or_default();
        }

        let offset = if self.offset.get() > 0 { self.offset.get() - 1 } else { 0 };

        match self.stream.get(offset) {
            Some(token) => token.span,
            None => self.stream.last().unwrap().span,
        }
    }

    /// Get the next location of the token, if there is no token after, we use
    /// the next character offset to determine the location.
    pub(crate) fn next_location(&self) -> Span {
        match self.peek() {
            Some(token) => token.span,
            None => {
                let span = self.current_location();
                Span::new(span.end(), span.end() + 1)
            }
        }
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    #[inline(always)]
    pub fn node<T>(&self, inner: T) -> AstNode<T> {
        AstNode::new(inner, self.current_location())
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    #[inline(always)]
    pub fn node_with_span<T>(&self, inner: T, location: Span) -> AstNode<T> {
        AstNode::new(inner, location)
    }

    /// Create a new [AstNode] with a span that ranges from the start [Span] to
    /// the current [Span].
    #[inline(always)]
    pub(crate) fn node_with_joined_span<T>(&self, body: T, start: &Span) -> AstNode<T> {
        AstNode::new(body, start.join(self.current_location()))
    }

    /// Create an error without wrapping it in an [Err] variant
    #[inline(always)]
    fn make_error(
        &self,
        kind: ParseErrorKind,
        expected: Option<TokenKindVector>,
        received: Option<TokenKind>,
        span: Option<Span>,
    ) -> ParseError {
        ParseError::new(
            kind,
            self.source_location(&span.unwrap_or_else(|| self.current_location())),
            expected,
            received,
        )
    }

    /// Create an error at the current location.
    pub(crate) fn error<T>(
        &self,
        kind: ParseErrorKind,
        expected: Option<TokenKindVector>,
        received: Option<TokenKind>,
    ) -> ParseResult<T> {
        Err(self.make_error(kind, expected, received, None))
    }

    /// Create an error at the current location.
    pub(crate) fn error_with_location<T>(
        &self,
        kind: ParseErrorKind,
        expected: Option<TokenKindVector>,
        received: Option<TokenKind>,
        span: Span,
    ) -> ParseResult<T> {
        Err(self.make_error(kind, expected, received, Some(span)))
    }

    /// Generate an error that represents that within the current [AstGen] the
    /// `end of file` state should be reached. This means that either in the
    /// root generator there are no more tokens or within a nested generator
    /// (such as if the generator is within a brackets) that it should now
    /// read no more tokens.
    pub(crate) fn expected_eof<T>(&self) -> ParseResult<T> {
        // move onto the next token
        self.offset.set(self.offset.get() + 1);
        self.error(ParseErrorKind::Eof, None, Some(self.current_token().kind))
    }

    /// Verify that the current [AstGen] has no more tokens.
    #[inline(always)]
    pub(crate) fn verify_is_empty(&self) -> ParseResult<()> {
        if self.has_token() {
            return self.expected_eof();
        }

        Ok(())
    }

    /// Generate an error representing that the current generator unexpectedly
    /// reached the end of input at this point.
    pub(crate) fn unexpected_eof<T>(&self) -> ParseResult<T> {
        self.error(ParseErrorKind::Eof, None, None)
    }

    /// Function to peek ahead and match some parsing function that returns a
    /// [Option<T>]. If The result is an error, the function wil reset the
    /// current offset of the token stream to where it was the function was
    /// peeked. This is essentially a convertor from a [AstGenResult<T>]
    /// into an [Option<T>] with the side effect of resetting the parser state
    /// back to it's original settings.
    pub(crate) fn peek_resultant_fn<T, E>(&self, parse_fn: impl Fn() -> Result<T, E>) -> Option<T> {
        let start = self.offset();

        match parse_fn() {
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
    pub(crate) fn parse_separated_fn<T>(
        &self,
        parse_fn: impl Fn() -> ParseResult<AstNode<T>>,
        separator_fn: impl Fn() -> ParseResult<()>,
    ) -> ParseResult<AstNodes<T>> {
        let start = self.current_location();
        let mut args = vec![];

        // so parse the arguments to the function here... with potential type
        // annotations
        while self.has_token() {
            match parse_fn() {
                Ok(el) => args.push(el),
                Err(err) => return Err(err),
            }

            if self.has_token() {
                separator_fn()?;
            }
        }

        Ok(AstNodes::new(args, Some(start.join(self.current_location()))))
    }

    /// Function to parse the next [Token] with the specified [TokenKind].
    pub(crate) fn parse_token(&self, atom: TokenKind) -> ParseResult<()> {
        match self.peek() {
            Some(token) if token.has_kind(atom) => {
                self.skip_token();
                Ok(())
            }
            token => self.error_with_location(
                ParseErrorKind::Expected,
                Some(TokenKindVector::singleton(atom)),
                token.map(|t| t.kind),
                token.map_or_else(|| self.next_location(), |t| t.span),
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

                let tree = self.token_trees.get(*tree_index).unwrap();
                Ok(self.from_stream(tree, *span))
            }
            token => self.error_with_location(
                error.unwrap_or(ParseErrorKind::Expected),
                Some(TokenKindVector::singleton(TokenKind::Delimiter(delimiter, true))),
                token.map(|tok| tok.kind),
                token.map_or_else(|| self.current_location(), |tok| tok.span),
            )?,
        }
    }

    /// Parse a [Module] which is simply made of a list of statements
    pub(crate) fn parse_module(&self) -> ParseResult<AstNode<Module>> {
        let start = self.current_location();
        let mut contents = vec![];

        while self.has_token() {
            contents.push(self.parse_top_level_expr(true).map(|(_, statement)| statement)?);
        }

        let span = start.join(self.current_location());
        Ok(self.node_with_span(Module { contents: AstNodes::new(contents, Some(span)) }, span))
    }

    /// This function is used to exclusively parse a interactive block which
    /// follows similar rules to a an actual block. Interactive statements
    /// are like ghost blocks without the actual braces to begin with. It
    /// follows that there are an arbitrary number of statements, followed
    /// by an optional final expression which doesn't need to be completed
    /// by a comma...
    pub(crate) fn parse_expr_from_interactive(&self) -> ParseResult<AstNode<BodyBlock>> {
        let start = self.current_location();

        let body = self.parse_body_block_inner()?;
        Ok(self.node_with_joined_span(body, &start))
    }
}
