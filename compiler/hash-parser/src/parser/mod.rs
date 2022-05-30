//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors
mod block;
mod definitions;
pub mod error;
mod expression;
mod literal;
mod name;
mod operator;
mod pattern;
mod types;

use std::cell::Cell;

use hash_alloc::{collections::row::Row, Wall};
use hash_ast::{
    ast::*,
    ast_nodes,
    ident::{Identifier, IDENTIFIER_MAP},
};
use hash_source::location::{SourceLocation, Span};
use hash_token::{Token, TokenKind, TokenKindVector};

use self::error::{AstGenError, AstGenErrorKind};
use crate::import_resolver::ImportResolver;

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

pub type AstGenResult<'a, T> = Result<T, AstGenError<'a>>;

pub struct AstGen<'c, 'stream, 'resolver> {
    /// Current token stream offset.
    offset: Cell<usize>,

    /// The span of the current generator, the root generator does not have a parent span,
    /// whereas as child generators might need to use the span to report errors if their
    /// token streams are empty (and they're expecting them to be non empty.) For example,
    /// if the expression `k[]` was being parsed, the index component `[]` is expected to be
    /// non-empty, so the error reporting can grab the span of the `[]` and report it as an
    /// expected expression.
    parent_span: Option<Span>,

    /// The token stream
    stream: &'stream [Token],

    /// Token trees that were generated from the stream
    token_trees: &'stream [Row<'stream, Token>],

    /// State set by expression parsers for parents to let them know if the parsed expression
    /// was made up of multiple expressions with precedence operators.
    is_compound_expr: Cell<bool>,

    /// Flag denoting whether spread patterns are allowed in the current context. This
    /// is only true if the parser is parsing either `tuple` or `list` patterns
    spread_patterns_allowed: Cell<bool>,

    /// Instance of an [ImportResolver] to notify the parser of encountered imports.
    resolver: &'resolver ImportResolver<'c>,

    /// The parser allocator
    wall: Wall<'c>,
}

/// Implementation of the [AstGen] with accompanying functions to parse specific
/// language components.
impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// Create new AST generator from a token stream.
    pub fn new(
        stream: &'stream [Token],
        token_trees: &'stream [Row<'stream, Token>],
        resolver: &'resolver ImportResolver<'c>,
        wall: Wall<'c>,
    ) -> Self {
        Self {
            stream,
            token_trees,
            parent_span: None,
            is_compound_expr: Cell::new(false),
            spread_patterns_allowed: Cell::new(false),
            offset: Cell::new(0),
            resolver,
            wall,
        }
    }

    /// Create new AST generator from a provided token stream with inherited module resolver
    /// and a provided parent span.
    #[must_use]
    pub fn from_stream(&self, stream: &'stream [Token], parent_span: Span) -> Self {
        Self {
            stream,
            token_trees: self.token_trees,
            offset: Cell::new(0),
            is_compound_expr: self.is_compound_expr.clone(),
            spread_patterns_allowed: self.spread_patterns_allowed.clone(),
            parent_span: Some(parent_span),
            resolver: self.resolver,
            wall: self.wall.owning_castle().wall(),
        }
    }

    /// Function to create a [SourceLocation] from a [Span] by using the provided resolver
    pub(crate) fn source_location(&self, span: &Span) -> SourceLocation {
        SourceLocation {
            span: *span,
            source_id: self.resolver.current_source_id(),
        }
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

    /// Function to check if the token stream has been exhausted based on the current
    /// offset in the generator.
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

    /// Get the current [Token] in the stream. Panics if the current offset has passed the
    /// size of the stream, e.g tring to get the current token after reaching the end of the
    /// stream.
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

    /// Get the current location from the current token, if there is no token at the current
    /// offset, then the location of the last token is used.
    pub(crate) fn current_location(&self) -> Span {
        // check that the length of current generator is at least one...
        if self.stream.is_empty() {
            return self.parent_span.unwrap_or_default();
        }

        let offset = if self.offset.get() > 0 { self.offset.get() - 1 } else { 0 };

        match self.stream.get(offset) {
            Some(token) => token.span,
            None => (*self.stream.last().unwrap()).span,
        }
    }

    /// Get the next location of the token, if there is no token after, we use the
    /// next character offset to determine the location.
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
    pub fn node<T>(&self, inner: T) -> AstNode<'c, T> {
        AstNode::new(inner, self.current_location(), &self.wall)
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    #[inline(always)]
    pub fn node_with_span<T>(&self, inner: T, location: Span) -> AstNode<'c, T> {
        AstNode::new(inner, location, &self.wall)
    }

    /// Create a new [AstNode] with a span that ranges from the start [Span] to the
    /// current [Span].
    #[inline(always)]
    pub(crate) fn node_with_joined_span<T>(&self, body: T, start: &Span) -> AstNode<'c, T> {
        AstNode::new(body, start.join(self.current_location()), &self.wall)
    }

    /// Create an error without wrapping it in an [Err] variant
    #[inline(always)]
    fn make_error(
        &self,
        kind: AstGenErrorKind,
        expected: Option<TokenKindVector<'c>>,
        received: Option<TokenKind>,
        location: Option<Span>,
    ) -> AstGenError<'c> {
        AstGenError::new(
            kind,
            self.source_location(&location.unwrap_or_else(|| self.current_location())),
            expected,
            received,
        )
    }

    /// Create an error at the current location.
    pub(crate) fn error<T>(
        &self,
        kind: AstGenErrorKind,
        expected: Option<TokenKindVector<'c>>,
        received: Option<TokenKind>,
    ) -> AstGenResult<'c, T> {
        Err(self.make_error(kind, expected, received, None))
    }

    /// Create an error at the current location.
    pub(crate) fn error_with_location<T>(
        &self,
        kind: AstGenErrorKind,
        expected: Option<TokenKindVector<'c>>,
        received: Option<TokenKind>,
        location: Span,
    ) -> AstGenResult<'c, T> {
        Err(self.make_error(kind, expected, received, Some(location)))
    }

    /// Generate an error that represents that within the current [AstGen] the
    /// `end of file` state should be reached. This means that either in the root
    /// generator there are no more tokens or within a nested generator (such as
    /// if the generator is within a brackets) that it should now read no more
    /// tokens.
    pub(crate) fn expected_eof<T>(&self) -> AstGenResult<'c, T> {
        // move onto the next token
        self.offset.set(self.offset.get() + 1);
        self.error(AstGenErrorKind::EOF, None, Some(self.current_token().kind))
    }

    /// Verify that the current [AstGen] has no more tokens.
    #[inline(always)]
    pub(crate) fn verify_is_empty(&self) -> AstGenResult<'c, ()> {
        if self.has_token() {
            return self.expected_eof();
        }

        Ok(())
    }

    /// Generate an error representing that the current generator unexpectedly reached the
    /// end of input at this point.
    pub(crate) fn unexpected_eof<T>(&self) -> AstGenResult<'c, T> {
        self.error(AstGenErrorKind::EOF, None, None)
    }

    /// Make an [Expression] with kind [ExpressionKind::Variable] from a specified identifier
    /// string.
    pub(crate) fn make_ident(&self, name: &str, location: &Span) -> AstNode<'c, Expression<'c>> {
        self.node_with_span(
            Expression::new(ExpressionKind::Variable(VariableExpr {
                name: self.make_access_name_from_str(name, *location),
                type_args: AstNodes::empty(),
            })),
            *location,
        )
    }

    /// Utility for creating a boolean in enum representation
    #[inline(always)]
    fn make_bool(&self, value: bool) -> AstNode<'c, Expression<'c>> {
        self.node(Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
            self.node(Literal::Bool(BoolLiteral(value))),
        ))))
    }

    /// Create an [AccessName] from a passed string.
    pub(crate) fn make_access_name_from_str<T: Into<String>>(
        &self,
        name: T,
        location: Span,
    ) -> AstNode<'c, AccessName<'c>> {
        let name = self.node_with_span(IDENTIFIER_MAP.create_ident(&name.into()), location);

        self.node_with_span(
            AccessName {
                path: ast_nodes![&self.wall; name],
            },
            location,
        )
    }

    /// Create a [AccessName] node from an [Identifier].
    pub(crate) fn make_access_name_from_identifier(
        &self,
        name: Identifier,
        location: Span,
    ) -> AstNode<'c, AccessName<'c>> {
        self.node_with_span(
            AccessName {
                path: ast_nodes![&self.wall; self.node_with_span(name, location)],
            },
            location,
        )
    }

    /// Function to peek ahead and match some parsing function that returns a [Option<T>].
    /// If The result is an error, the function wil reset the current offset of the token stream
    /// to where it was the function was peeked. This is essentially a convertor from a [AstGenResult<T>]
    /// into an [Option<T>] with the side effect of resetting the parser state back to it's original
    /// settings.
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

    /// Function to parse an arbitrary number of 'parsing functions' separated by a singular
    /// 'separator' closure. The function has a behaviour of allowing trailing separator. This
    /// will also parse the function until the end of the current generator, and therefore it
    /// is intended to be used with a nested generator.
    pub(crate) fn parse_separated_fn<T>(
        &self,
        parse_fn: impl Fn() -> AstGenResult<'c, AstNode<'c, T>>,
        separator_fn: impl Fn() -> AstGenResult<'c, ()>,
    ) -> AstGenResult<'c, AstNodes<'c, T>> {
        let start = self.current_location();
        let mut args = vec![];

        // so parse the arguments to the function here... with potential type annotations
        while self.has_token() {
            match parse_fn() {
                Ok(el) => args.push(el),
                Err(err) => return Err(err),
            }

            if self.has_token() {
                separator_fn()?;
            }
        }

        Ok(AstNodes::new(
            Row::from_vec(args, &self.wall),
            Some(start.join(self.current_location())),
        ))
    }

    /// Function to parse the next [Token] with the specified [TokenKind].
    pub(crate) fn parse_token(&self, atom: TokenKind) -> AstGenResult<'c, ()> {
        match self.peek() {
            Some(token) if token.has_kind(atom) => {
                self.skip_token();
                Ok(())
            }
            Some(token) => self.error_with_location(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::singleton(&self.wall, atom)),
                Some(token.kind),
                token.span,
            ),
            _ => self.error(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::singleton(&self.wall, atom)),
                None,
            ),
        }
    }

    /// Function to parse a token atom optionally. If the appropriate token atom is
    /// present we advance the token count, if not then just return None
    pub(crate) fn parse_token_fast(&self, kind: TokenKind) -> Option<()> {
        match self.peek() {
            Some(token) if token.has_kind(kind) => {
                self.skip_token();
                Some(())
            }
            _ => None,
        }
    }

    /// Parse a [Module] which is simply made of a list of statements
    pub(crate) fn parse_module(&self) -> AstGenResult<'c, AstNode<'c, Module<'c>>> {
        let start = self.current_location();
        let mut contents = vec![];

        while self.has_token() {
            contents.push(
                self.parse_top_level_expression(true)
                    .map(|(_, statement)| statement)?,
            );
        }

        let span = start.join(self.current_location());
        Ok(self.node_with_span(
            Module {
                contents: AstNodes::new(Row::from_vec(contents, &self.wall), Some(span)),
            },
            span,
        ))
    }

    /// This function is used to exclusively parse a interactive block which follows
    /// similar rules to a an actual block. Interactive statements are like ghost blocks
    /// without the actual braces to begin with. It follows that there are an arbitrary
    /// number of statements, followed by an optional final expression which doesn't
    /// need to be completed by a comma...
    pub(crate) fn parse_expression_from_interactive(
        &self,
    ) -> AstGenResult<'c, AstNode<'c, BodyBlock<'c>>> {
        // get the starting position
        let start = self.current_location();

        let block = self.parse_block_from_gen(self, start, None)?;

        // We just need to unwrap the BodyBlock from Block since parse_block_from_gen is generic...
        match block.into_body().move_out() {
            Block::Body(body) => Ok(self.node_with_joined_span(body, &start)),
            _ => unreachable!(),
        }
    }
}
