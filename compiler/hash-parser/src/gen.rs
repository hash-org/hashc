//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_alloc::collections::row::Row;
use hash_alloc::{row, Wall};
use hash_ast::{
    ast::*,
    ident::{Identifier, IDENTIFIER_MAP},
    keyword::Keyword,
    literal::STRING_LITERAL_MAP,
};
use hash_ast::{ast_nodes, operator::Operator};
use hash_ast::{ident::CORE_IDENTIFIERS, operator::OperatorKind};
use hash_source::location::{Location, SourceLocation};
use std::cell::Cell;
use std::path::PathBuf;
use std::str::FromStr;

use crate::parser::ImportResolver;
use crate::token::{Delimiter, Token, TokenKindVector};
use crate::{
    error::{AstGenError, AstGenErrorKind, TyArgumentKind},
    token::TokenKind,
};

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
    parent_span: Option<Location>,

    /// The token stream
    stream: &'stream [Token],

    /// Token trees that were generated from the stream
    token_trees: &'stream [Row<'stream, Token>],

    /// State set by expression parsers for parents to let them know if the parsed expression
    /// was made up of multiple expressions with precedence operators.
    is_compound_expr: Cell<bool>,

    /// State to prevent from struct literals being parsed in the current expression, because
    /// the parent has specifically checked ahead to ensure it isn't a struct literal.
    disallow_struct_literals: Cell<bool>,

    /// Instance of an [ImportResolver] to notify the parser of encountered imports.
    resolver: &'resolver ImportResolver<'c>,

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
            disallow_struct_literals: Cell::new(false),
            offset: Cell::new(0),
            resolver,
            wall,
        }
    }

    /// Create new AST generator from a provided token stream with inherited module resolver
    /// and a provided parent span.
    #[must_use]
    pub fn from_stream(&self, stream: &'stream [Token], parent_span: Location) -> Self {
        Self {
            stream,
            token_trees: self.token_trees,
            offset: Cell::new(0),
            is_compound_expr: Cell::new(false),
            disallow_struct_literals: Cell::new(false),
            parent_span: Some(parent_span),
            resolver: self.resolver,
            wall: self.wall.owning_castle().wall(),
        }
    }

    /// Function to create a [SourceLocation] from a [Location] by using the provided resolver
    fn source_location(&self, location: &Location) -> SourceLocation {
        SourceLocation {
            location: *location,
            source_id: self.resolver.current_source_id(),
        }
    }

    /// Get the current offset of where the stream is at.
    #[inline(always)]
    pub(crate) fn offset(&self) -> usize {
        self.offset.get()
    }

    /// Function to peek at the nth token ahead of the current offset.
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
            // @@UnsafeLibUsage
            self.offset.update::<_>(|x| x + 1);
        }

        value
    }

    /// Get the current token in the stream.
    pub(crate) fn current_token(&self) -> &Token {
        let offset = if self.offset.get() > 0 { self.offset.get() - 1 } else { 0 };

        self.stream.get(offset).unwrap()
    }

    /// Get the current location from the current token, if there is no token at the current
    /// offset, then the location of the last token is used.
    pub(crate) fn current_location(&self) -> Location {
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
    pub(crate) fn next_location(&self) -> Location {
        match self.peek() {
            Some(token) => token.span,
            None => {
                let Token { span, kind: _ } = self.current_token();
                Location::span(span.end(), span.end() + 1)
            }
        }
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    pub fn node<T>(&self, inner: T) -> AstNode<'c, T> {
        AstNode::new(inner, self.current_location(), &self.wall)
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    pub fn node_with_location<T>(&self, inner: T, location: Location) -> AstNode<'c, T> {
        AstNode::new(inner, location, &self.wall)
    }

    /// Create an error at the current location.
    pub fn error<T>(
        &self,
        kind: AstGenErrorKind,
        expected: Option<TokenKindVector<'c>>,
        received: Option<TokenKind>,
    ) -> AstGenResult<'c, T> {
        Err(AstGenError::new(
            kind,
            self.source_location(&self.current_location()),
            expected,
            received,
        ))
    }

    /// Create an error at the current location.
    pub fn error_with_location<T>(
        &self,
        kind: AstGenErrorKind,
        expected: Option<TokenKindVector<'c>>,
        received: Option<TokenKind>,
        location: &Location,
    ) -> AstGenResult<'c, T> {
        Err(AstGenError::new(
            kind,
            self.source_location(location),
            expected,
            received,
        ))
    }

    pub(crate) fn expected_eof<T>(&self) -> AstGenResult<'c, T> {
        // move onto the next token
        self.offset.set(self.offset.get() + 1);

        self.error(
            AstGenErrorKind::EOF,
            Some(TokenKindVector::singleton(
                &self.wall,
                self.current_token().kind,
            )),
            None,
        )
    }

    /// Create a generalised "Reached end of file..." error.
    pub(crate) fn unexpected_eof<T>(&self) -> AstGenResult<'c, T> {
        self.error(AstGenErrorKind::EOF, None, None)
    }

    /// Make an [Expression] with kind [ExpressionKind::Variable] from a specified identifier
    /// string.
    pub(crate) fn make_ident(
        &self,
        name: &str,
        location: &Location,
    ) -> AstNode<'c, Expression<'c>> {
        self.node_from_location(
            Expression::new(ExpressionKind::Variable(VariableExpr {
                name: self.make_access_name_from_str(name, *location),
                type_args: AstNodes::empty(),
            })),
            location,
        )
    }

    fn make_enum_pattern_from_str<T: Into<String>>(
        &self,
        symbol: T,
        location: Location,
    ) -> AstNode<'c, Pattern<'c>> {
        self.node(Pattern::Enum(EnumPattern {
            name: self.make_access_name_from_str(symbol, location),
            args: AstNodes::empty(),
        }))
    }

    /// Utility function for creating a variable from a given name.
    fn make_variable(&self, name: AstNode<'c, AccessName<'c>>) -> AstNode<'c, Expression<'c>> {
        self.node(Expression::new(ExpressionKind::Variable(VariableExpr {
            name,
            type_args: AstNodes::empty(),
        })))
    }

    /// Utility for creating a boolean in enum representation
    fn make_boolean(&self, variant: bool) -> AstNode<'c, AccessName<'c>> {
        let name_ref = match variant {
            false => "false",
            true => "true",
        };

        self.node(AccessName {
            path: row![&self.wall; IDENTIFIER_MAP.create_ident(name_ref)],
        })
    }

    /// Create an [AccessName] from a passed string.
    pub(crate) fn make_access_name_from_str<T: Into<String>>(
        &self,
        name: T,
        location: Location,
    ) -> AstNode<'c, AccessName<'c>> {
        let name = IDENTIFIER_MAP.create_ident(&name.into());

        self.node_with_location(
            AccessName {
                path: row![&self.wall; name],
            },
            location,
        )
    }

    /// Create a [AccessName] node from an [Identifier].
    pub(crate) fn make_access_name_from_identifier(
        &self,
        name: Identifier,
        location: Location,
    ) -> AstNode<'c, AccessName<'c>> {
        self.node_with_location(
            AccessName {
                path: row![&self.wall; name],
            },
            location,
        )
    }

    /// Make an [Expression] with kind [ExpressionKind::Variable] from a provided [Identifier] with a provided span.
    pub(crate) fn make_variable_from_identifier(
        &self,
        id: Identifier,
        location: Location,
    ) -> AstNode<'c, Expression<'c>> {
        AstNode::new(
            Expression::new(ExpressionKind::Variable(VariableExpr {
                name: self.node_from_joined_location(
                    AccessName {
                        path: row![&self.wall; id],
                    },
                    &location,
                ),
                type_args: AstNodes::empty(),
            })),
            location,
            &self.wall,
        )
    }

    pub(crate) fn node_from_location<T>(&self, body: T, location: &Location) -> AstNode<'c, T> {
        AstNode::new(body, *location, &self.wall)
    }

    pub(crate) fn node_from_joined_location<T>(&self, body: T, start: &Location) -> AstNode<'c, T> {
        AstNode::new(body, start.join(self.current_location()), &self.wall)
    }

    /// Function to peek ahead and match some parsing function that returns a [Option<T>] wrapped
    /// in a [AstGenResult]. If The result is an error, or the option is [None], the function will
    /// reset the current offset of the token stream to where it was the function was peeked.
    pub fn peek_fn<T>(
        &self,
        parse_fn: impl Fn() -> AstGenResult<'c, Option<T>>,
    ) -> AstGenResult<'c, Option<T>> {
        let start = self.offset();

        match parse_fn() {
            result @ Ok(Some(_)) => result,
            err => {
                self.offset.set(start);
                err
            }
        }
    }

    /// Function to peek ahead and match some parsing function that returns a [Option<T>].
    /// If The result is an error, the function wil reset the current offset of the token stream
    /// to where it was the function was peeked. This is essentially a convertor from a [AstGenResult<T>]
    /// into an [Option<T>] with the side effect of resetting the parser state back to it's original
    /// settings.
    pub fn peek_resultant_fn<T, E>(&self, parse_fn: impl Fn() -> Result<T, E>) -> Option<T> {
        let start = self.offset();

        match parse_fn() {
            Ok(result) => Some(result),
            Err(_) => {
                self.offset.set(start);
                None
            }
        }
    }

    /// Parse a [Module] which is simply made of a list of statements
    pub fn parse_module(&self) -> AstGenResult<'c, AstNode<'c, Module<'c>>> {
        let start = self.current_location();
        let mut contents = AstNodes::empty();

        while self.has_token() {
            contents.nodes.push(self.parse_statement()?, &self.wall);
        }

        let span = start.join(self.current_location());
        contents.span = Some(span);

        Ok(self.node_with_location(Module { contents }, span))
    }

    /// Parse a statement.
    pub fn parse_statement(&self) -> AstGenResult<'c, AstNode<'c, Statement<'c>>> {
        let start = self.current_location();

        match self.peek() {
            Some(Token { kind, span: _ }) if kind.begins_statement() => {
                self.skip_token();

                let statement = match kind {
                    TokenKind::Keyword(Keyword::Let) => Statement::Let(self.parse_let_statement()?),
                    TokenKind::Keyword(Keyword::Trait) => {
                        Statement::TraitDef(self.parse_trait_defn()?)
                    }
                    TokenKind::Keyword(Keyword::Enum) => {
                        Statement::EnumDef(self.parse_enum_defn()?)
                    }
                    TokenKind::Keyword(Keyword::Struct) => {
                        Statement::StructDef(self.parse_struct_defn()?)
                    }
                    TokenKind::Keyword(Keyword::Continue) => Statement::Continue(ContinueStatement),
                    TokenKind::Keyword(Keyword::Break) => Statement::Break(BreakStatement),
                    TokenKind::Keyword(Keyword::Return) => {
                        // @@Hack: check if the next token is a semi-colon, if so the return statement
                        // has no returned expression...
                        match self.peek() {
                            Some(token) if token.has_kind(TokenKind::Semi) => {
                                Statement::Return(ReturnStatement(None))
                            }
                            Some(_) => Statement::Return(ReturnStatement(Some(
                                self.parse_expression_with_precedence(0)?,
                            ))),
                            None => Statement::Return(ReturnStatement(None)),
                        }
                    }
                    _ => unreachable!(),
                };

                let current_location = self.current_location();

                // USE PREV token location
                match self.next_token() {
                    Some(token) if token.has_kind(TokenKind::Semi) => {
                        Ok(self.node_from_location(statement, &start.join(current_location)))
                    }
                    Some(token) => self.error_with_location(
                        AstGenErrorKind::Expected,
                        Some(TokenKindVector::begin_expression(&self.wall)),
                        Some(token.kind),
                        &current_location,
                    ),
                    None => self.error(AstGenErrorKind::EOF, None, Some(*kind))?,
                }
            }
            Some(_) => {
                let lhs = self.parse_expression_with_precedence(0)?;
                let (expr, re_assigned) = self.try_parse_re_assignment_operation(lhs)?;

                if re_assigned {
                    let current_location = self.current_location(); // We don't want to include the semi in the current span
                    self.parse_token_atom(TokenKind::Semi)?;

                    return Ok(self.node_from_location(
                        Statement::Expr(ExprStatement(expr)),
                        &start.join(current_location),
                    ));
                }

                // Ensure that the next token is a Semi
                match self.peek() {
                    Some(token) if token.has_kind(TokenKind::Semi) => {
                        let current_location = self.current_location(); // We don't want to include the semi in the current span
                        self.skip_token();

                        Ok(self.node_from_location(
                            Statement::Expr(ExprStatement(expr)),
                            &start.join(current_location),
                        ))
                    }
                    Some(token) if token.has_kind(TokenKind::Eq) => {
                        self.skip_token();

                        // Parse the rhs and the semi
                        let rhs = self.parse_expression_with_precedence(0)?;
                        self.parse_token_atom(TokenKind::Semi)?;

                        Ok(self.node_from_joined_location(
                            Statement::Assign(AssignStatement { lhs: expr, rhs }),
                            &start,
                        ))
                    }

                    // Special case where there is a expression at the end of the stream and therefore it
                    // is signifying that it is returning the expression value here
                    None => {
                        Ok(self.node_from_location(Statement::Expr(ExprStatement(expr)), &start))
                    }

                    token => match (token, expr.into_body().move_out().into_kind()) {
                        (_, ExpressionKind::Block(BlockExpr(block))) => Ok(self
                            .node_from_location(Statement::Block(BlockStatement(block)), &start)),
                        (Some(token), _) => self.error(
                            AstGenErrorKind::Expected,
                            Some(TokenKindVector::begin_expression(&self.wall)),
                            Some(token.kind),
                        ),
                        (None, _) => unreachable!(),
                    },
                }
            }
            None => self.error(AstGenErrorKind::ExpectedStatement, None, None)?,
        }
    }

    /// Given a initial left-hand side expression, attempt to parse a re-assignment operator and
    /// then right hand-side. If a re-assignment operator is successfully parsed, then a right
    /// hand-side is expected and will hard fail. If no re-assignment operator is found, then it
    /// should just return the left-hand side.
    fn try_parse_re_assignment_operation(
        &self,
        lhs: AstNode<'c, Expression<'c>>,
    ) -> AstGenResult<'c, (AstNode<'c, Expression<'c>>, bool)> {
        if let Some(op) = self.peek_resultant_fn(|| self.parse_re_assignment_op()) {
            // Parse the rhs and the semi
            let rhs = self.parse_expression_with_precedence(0)?;

            // Now we need to transform the re-assignment operator into a function call
            Ok((self.transform_binary_expression(lhs, rhs, op), false))
        } else {
            Ok((lhs, false))
        }
    }

    /// This function is used to exclusively parse a interactive block which follows
    /// similar rules to a an actual block. Interactive statements are like ghost blocks
    /// without the actual braces to begin with. It follows that there are an arbitrary
    /// number of statements, followed by an optional final expression which doesn't
    /// need to be completed by a comma...
    pub fn parse_expression_from_interactive(
        &self,
    ) -> AstGenResult<'c, AstNode<'c, BodyBlock<'c>>> {
        // get the starting position
        let start = self.current_location();

        let block = self.parse_block_from_gen(self, start, None)?;

        // We just need to unwrap the BodyBlock from Block since parse_block_from_gen is generic...
        match block.into_body().move_out() {
            Block::Body(body) => Ok(self.node_from_joined_location(body, &start)),
            _ => unreachable!(),
        }
    }

    /// Utility function to transform to some expression into a referenced expression
    /// given some condition. This function is useful when transpiling some types of
    /// operators which might have a side-effect to overwrite the lhs.
    fn transform_expr_into_ref(
        &self,
        expr: AstNode<'c, Expression<'c>>,
        transform: bool,
    ) -> AstNode<'c, Expression<'c>> {
        match transform {
            true => self.node(Expression::new(ExpressionKind::Ref(RefExpr {
                inner_expr: expr,
                kind: RefKind::Normal,
            }))),
            false => expr,
        }
    }

    /// Create an [Expression] from two provided expressions and an [OperatorFn].
    fn transform_binary_expression(
        &self,
        lhs: AstNode<'c, Expression<'c>>,
        rhs: AstNode<'c, Expression<'c>>,
        op: AstNode<'c, Operator>,
    ) -> AstNode<'c, Expression<'c>> {
        let Operator { kind, assignable } = op.body();

        if kind.is_compound() {
            // for compound functions that include ordering, we essentially transpile
            // into a match block that checks the result of the 'ord' fn call to the
            // 'Ord' enum variants. This also happens for operators such as '>=' which
            // essentially means that we have to check if the result of 'ord()' is either
            // 'Eq' or 'Gt'.
            self.transform_compound_ord_fn(*kind, *assignable, lhs, rhs)
        } else if kind.is_lazy() {
            // some functions have to exhibit a short-circuiting behaviour, namely
            // the logical 'and' and 'or' operators. To do this, we expect the 'and'
            // 'or' trait (and their assignment counterparts) to expect the rhs part
            // as a lambda. So, we essentially create a lambda that calls the rhs, or
            // in other words, something like this happens:
            //
            // >>> lhs && rhs
            // vvv (transpiles to...)
            // >>> and(lhs, () => rhs)
            //
            let location = lhs.location().join(rhs.location());

            self.node_from_location(Expression::new(ExpressionKind::FunctionCall(
                    FunctionCallExpr {
                        subject: self.node_from_location(
                            Expression::new(ExpressionKind::Variable(VariableExpr {
                                name: self.make_access_name_from_str(kind.to_string(), op.location()),
                                type_args: AstNodes::empty(),
                            })),
                            &op.location(),
                        ),
                        args: self.node_from_joined_location(
                            FunctionCallArgs {
                            entries: ast_nodes![&self.wall;
                                self.transform_expr_into_ref(lhs, *assignable),
                                self.node(Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(self.node(
                                    Literal::Function(FunctionDef {
                                        args: AstNodes::empty(),
                                        return_ty: None,
                                        fn_body: rhs,
                                    }),
                                )))))
                            ],
                        },  &location),
                    },
                )), &location)
        } else {
            let location = lhs.location().join(rhs.location());

            self.node_from_location(
                Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.node_from_location(
                        Expression::new(ExpressionKind::Variable(VariableExpr {
                            name: self.make_access_name_from_str(kind.to_string(), op.location()),
                            type_args: AstNodes::empty(),
                        })),
                        &op.location(),
                    ),
                    args: self.node_from_joined_location(
                        FunctionCallArgs {
                            entries: ast_nodes![&self.wall;
                                self.transform_expr_into_ref(lhs, *assignable),
                                rhs,
                            ],
                        },
                        &location,
                    ),
                })),
                &op.location(),
            )
        }
    }

    fn transform_compound_ord_fn(
        &self,
        fn_ty: OperatorKind,
        assigning: bool,
        lhs: AstNode<'c, Expression<'c>>,
        rhs: AstNode<'c, Expression<'c>>,
    ) -> AstNode<'c, Expression<'c>> {
        let location = lhs.location().join(rhs.location());

        // we need to transform the lhs into a reference if the type of function is 'assigning'
        let lhs = self.transform_expr_into_ref(lhs, assigning);

        let fn_call = self.node(Expression::new(ExpressionKind::FunctionCall(
            FunctionCallExpr {
                subject: self.make_ident("ord", &location),
                args: self.node(FunctionCallArgs {
                    entries: ast_nodes![&self.wall; lhs, rhs],
                }),
            },
        )));

        // each tuple bool variant represents a branch the match statement
        // should return 'true' on, and all the rest will return false...
        // the order is (Lt, Eq, Gt)
        let mut branches = match fn_ty {
            OperatorKind::LtEq => {
                ast_nodes![&self.wall; self.node(MatchCase {
                    pattern: self.node(Pattern::Or(OrPattern {
                        variants: ast_nodes![&self.wall;
                        self.make_enum_pattern_from_str("Lt", location),
                        self.make_enum_pattern_from_str("Eq", location),
                        ],
                    })),
                    expr: self.make_variable(self.make_boolean(true)),
                })]
            }
            OperatorKind::GtEq => {
                ast_nodes![&self.wall; self.node(MatchCase {
                    pattern: self.node(Pattern::Or(OrPattern {
                        variants: ast_nodes![&self.wall;
                        self.make_enum_pattern_from_str("Gt", location),
                        self.make_enum_pattern_from_str("Eq", location),
                        ],
                    })),
                    expr: self.make_variable(self.make_boolean(true)),
                })]
            }
            OperatorKind::Lt => {
                ast_nodes![&self.wall; self.node(MatchCase {
                    pattern: self.make_enum_pattern_from_str("Lt", location),
                    expr: self.make_variable(self.make_boolean(false)),
                })]
            }
            OperatorKind::Gt => {
                ast_nodes![&self.wall; self.node(MatchCase {
                    pattern: self.make_enum_pattern_from_str("Gt", location),
                    expr: self.make_variable(self.make_boolean(false)),
                })]
            }
            _ => unreachable!(),
        };

        // add the '_' case to the branches to return false on any other
        // condition
        branches.nodes.push(
            self.node(MatchCase {
                pattern: self.node(Pattern::Ignore(IgnorePattern)),
                expr: self.make_variable(self.make_boolean(false)),
            }),
            &self.wall,
        );

        self.node(Expression::new(ExpressionKind::Block(BlockExpr(
            self.node(Block::Match(MatchBlock {
                subject: fn_call,
                cases: branches,
            })),
        ))))
    }

    /// Function to parse an arbitrary number of 'parsing functions' separated by a singular
    /// 'separator' closure. The function has a behaviour of allowing trailing separator. This
    /// will also parse the function until the end of the current generator, and therefore it
    /// is intended to be used with a nested generator.
    pub fn parse_separated_fn<T>(
        &self,
        parse_fn: impl Fn() -> AstGenResult<'c, AstNode<'c, T>>,
        separator_fn: impl Fn() -> AstGenResult<'c, ()>,
    ) -> AstGenResult<'c, AstNodes<'c, T>> {
        let mut args = AstNodes::empty();
        let start = self.current_location();

        // so parse the arguments to the function here... with potential type annotations
        while self.has_token() {
            match parse_fn() {
                Ok(el) => args.nodes.push(el, &self.wall),
                Err(err) => return Err(err),
            }

            if self.has_token() {
                separator_fn()?;
            }
        }

        if self.has_token() {
            self.expected_eof()?;
        }

        args.span = Some(start.join(self.current_location()));
        Ok(args)
    }

    /// This will parse an operator and check that it is re-assignable, if the operator is not
    /// re-assignable then the result of the function is an [AstGenError] since it expects there
    /// to be this operator.
    pub fn parse_re_assignment_op(&self) -> AstGenResult<'c, AstNode<'c, Operator>> {
        let start = self.next_location();
        let (operator, consumed_tokens) = self.parse_operator();

        match operator {
            Some(Operator {
                kind,
                assignable: true,
            }) => {
                // consume the number of tokens eaten whilst getting the operator...
                self.offset.update(|x| x + consumed_tokens as usize);

                Ok(self.node_from_joined_location(
                    Operator {
                        kind,
                        assignable: true,
                    },
                    &start,
                ))
            }
            _ => self.error(AstGenErrorKind::ReAssignmentOp, None, None), // TODO: actually add information here
        }
    }

    /// Parse a trait definition. AST representation of a trait statement.
    /// A trait statement is essentially a function with no body, with a
    /// for-all node and some genetic type arguments. For example,
    ///
    /// trait eq<T> => (T, T) => bool;
    ///     ┌─^^ ^─┐   ^─ ─ ─ ─ ─ ─ ─ ┐
    ///   name   Generic type args    Function type definition
    pub fn parse_trait_defn(&self) -> AstGenResult<'c, TraitDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Trait)));

        let name = self.parse_ident()?;

        self.parse_token_atom(TokenKind::Eq)?;
        let bound = self.parse_type_bound()?;

        self.parse_arrow()?; // the next token should be a TokenTree delimited with an arrow.

        let trait_type = self.parse_function_or_tuple_type(true)?;

        Ok(TraitDef {
            name,
            bound,
            trait_type,
        })
    }

    /// AST representation of a struct which includes the name of the struct with a
    /// ForAll to specify any bounds or and generic arguments to the struct, with
    /// zero or more struct fields. An example for a struct would be:
    ///
    /// struct Name <T,Q> where eq<T> { ... };
    ///        ^^^^    ^──────^^─┬──^   ^^^
    /// Name of struct        For all  fields
    ///
    pub fn parse_struct_defn(&self) -> AstGenResult<'c, StructDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Struct)));

        let name = self.parse_ident()?;
        self.parse_token_atom(TokenKind::Eq)?;

        let (bound, entries) = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Lt) => {
                let bound = Some(self.parse_type_bound()?);
                self.parse_arrow()?;
                let entries = self.parse_struct_def_entries()?;

                (bound, entries)
            }

            Some(token) if token.is_brace_tree() => {
                let entries = self.parse_struct_def_entries()?;

                (None, entries)
            }
            token => self.error(
                AstGenErrorKind::TyArgument(TyArgumentKind::Struct),
                None,
                token.map(|tok| tok.kind),
            )?,
        };

        Ok(StructDef {
            name,
            bound,
            entries,
        })
    }

    /// Parse an enum definition. AST representation for an enum, An enum is constructed by
    /// a the keyword 'enum' followed by an identifier name, a for-all declaration,
    /// followed by some enum fields. An enumeration can be made of zero or more enum fields.
    /// For example, a declaration of an enum would be:
    ///
    /// enum Name<T,Q> where eq<T> => { ... };
    ///      ^^^^  ^──────^^─┬──^       ^^^
    /// Name of enum      For all      fields
    ///
    pub fn parse_enum_defn(&self) -> AstGenResult<'c, EnumDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Enum)));

        let name = self.parse_ident()?;

        self.parse_token_atom(TokenKind::Eq)?;

        // now parse the optional type bound and the enum definition entries,
        // if a type bound is specified, then the definition of the struct should
        // be followed by an arrow ('=>')...
        let (bound, entries) = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Lt) => {
                let bound = Some(self.parse_type_bound()?);
                self.parse_arrow()?;

                let entries = self.parse_enum_def_entries()?;

                (bound, entries)
            }

            Some(token) if token.is_brace_tree() => {
                let entries = self.parse_enum_def_entries()?;

                (None, entries)
            }
            token => self.error(
                AstGenErrorKind::TyArgument(TyArgumentKind::Enum),
                None,
                token.map(|tok| tok.kind),
            )?,
        };

        Ok(EnumDef {
            name,
            bound,
            entries,
        })
    }

    pub fn parse_enum_def_entries(&self) -> AstGenResult<'c, AstNodes<'c, EnumDefEntry<'c>>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            }) => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, *span);

                gen.parse_separated_fn(
                    || gen.parse_enum_def_entry(),
                    || gen.parse_token_atom(TokenKind::Comma),
                )
            }
            Some(token) => self.error(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::singleton(
                    &self.wall,
                    TokenKind::Delimiter(Delimiter::Brace, false),
                )),
                Some(token.kind),
            ),
            None => self.unexpected_eof(),
        }
    }

    /// Parse an Enum definition entry.
    pub fn parse_enum_def_entry(&self) -> AstGenResult<'c, AstNode<'c, EnumDefEntry<'c>>> {
        let start = self.current_location();
        let name = self.parse_ident()?;

        let mut args = AstNodes::empty();

        if let Some(Token {
            kind: TokenKind::Tree(Delimiter::Paren, tree_index),
            span,
        }) = self.peek()
        {
            self.skip_token();
            args.span = Some(*span);
            let tree = self.token_trees.get(*tree_index).unwrap();

            let gen = self.from_stream(tree, *span);
            while gen.has_token() {
                let ty = gen.parse_type()?;
                args.nodes.push(ty, &self.wall);

                if gen.has_token() {
                    gen.parse_token_atom(TokenKind::Comma)?;
                }
            }
        }

        Ok(self.node_from_joined_location(EnumDefEntry { name, args }, &start))
    }

    /// Parse struct definition field entries.
    pub fn parse_struct_def_entries(&self) -> AstGenResult<'c, AstNodes<'c, StructDefEntry<'c>>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            }) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, *span);

                gen.parse_separated_fn(
                    || gen.parse_struct_def_entry(),
                    || gen.parse_token_atom(TokenKind::Comma),
                )
            }
            Some(token) => {
                let atom = token.kind;
                let expected = TokenKindVector::from_row(
                    row![&self.wall; TokenKind::Delimiter(Delimiter::Brace, true)],
                );

                self.error(AstGenErrorKind::Expected, Some(expected), Some(atom))?
            }
            None => self.unexpected_eof(),
        }
    }

    /// Parse struct definition field.
    pub fn parse_struct_def_entry(&self) -> AstGenResult<'c, AstNode<'c, StructDefEntry<'c>>> {
        let start = self.current_location();
        let name = self.parse_ident()?;

        let ty = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Colon) => {
                self.skip_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        let default = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Eq) => {
                self.skip_token();

                Some(self.parse_expression_with_precedence(0)?)
            }
            _ => None,
        };

        Ok(self.node_from_joined_location(StructDefEntry { name, ty, default }, &start))
    }

    /// Parse a type bound. Type bounds can occur in traits, function, struct and enum
    /// definitions.
    pub fn parse_type_bound(&self) -> AstGenResult<'c, AstNode<'c, Bound<'c>>> {
        let start = self.current_location();
        let type_args = self.parse_type_args()?;

        let trait_bounds = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Where)) => {
                self.skip_token();

                let mut trait_bounds = ast_nodes![&self.wall;];

                loop {
                    match self.peek() {
                        Some(Token {
                            kind: TokenKind::Ident(ident),
                            span: _,
                        }) => {
                            self.skip_token();

                            let bound_start = self.current_location();
                            let (name, type_args) = self.parse_trait_bound(ident)?;

                            trait_bounds.nodes.push(
                                self.node_from_joined_location(
                                    TraitBound { name, type_args },
                                    &bound_start,
                                ),
                                &self.wall,
                            );

                            // ensure that the bound is followed by a comma, if not then break...
                            match self.peek() {
                                Some(token) if token.has_kind(TokenKind::Comma) => {
                                    self.skip_token();
                                }
                                _ => break,
                            }
                        }
                        None => self.unexpected_eof()?,
                        _ => break,
                    }
                }

                trait_bounds
            }
            _ => ast_nodes![&self.wall;],
        };

        Ok(self.node_from_joined_location(
            Bound {
                type_args,
                trait_bounds,
            },
            &start,
        ))
    }

    /// transpile the for-loop into a simpler loop as described by the documentation.
    /// Since for loops are used for iterators in hash, we transpile the construct into a primitive loop.
    /// An iterator can be traversed by calling the next function on the iterator.
    /// Since next returns a Option type, we need to check if there is a value or if it returns None.
    /// If a value does exist, we essentially perform an assignment to the pattern provided.
    /// If None, the branch immediately breaks the for loop.
    ///
    /// A rough outline of what the transpilation process for a for loop looks like:
    ///
    /// For example, the for loop can be expressed using loop as:
    ///
    /// >>> for <pat> in <iterator> {
    /// >>>     <block>
    /// >>> }
    ///
    /// converted to:
    /// >>> loop {
    /// >>>     match next(<iterator>) {
    /// >>>         Some(<pat>) => <block>;
    /// >>>         None        => break;
    /// >>>     }
    /// >>> }
    pub fn parse_for_loop(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::For)));

        let start = self.current_location();

        // now we parse the singular pattern that begins at the for-loop
        let pattern = self.parse_pattern()?;
        let pattern_location = pattern.location();

        self.parse_token_atom(TokenKind::Keyword(Keyword::In))?;

        self.disallow_struct_literals.set(true);
        let iterator = self.parse_expression_with_precedence(0)?;
        let iterator_location = iterator.location();
        self.disallow_struct_literals.set(false);

        let body = self.parse_block()?;
        let body_location = body.location();

        // transpile the for loop
        Ok(self.node_from_joined_location(Block::Loop(LoopBlock(self.node_from_location(
            Block::Match(MatchBlock {
            subject: self.node(Expression::new(ExpressionKind::FunctionCall(
                FunctionCallExpr {
                    subject: self.node(Expression::new(ExpressionKind::Variable(
                        VariableExpr {
                            name: self.make_access_name_from_str("next", iterator.location()),
                            type_args: AstNodes::empty(),
                        },
                    ))),
                    args: self.node_from_location(FunctionCallArgs {
                        entries: ast_nodes![&self.wall; iterator],
                    }, &iterator_location),
                },
            ))),
            cases: ast_nodes![&self.wall; self.node_from_location(MatchCase {
                    pattern: self.node_from_location(
                        Pattern::Enum(
                            EnumPattern {
                                name:
                                    self.make_access_name_from_str(
                                        "Some",
                                        self.current_location()
                                    ),
                                args: ast_nodes![&self.wall; pattern],
                            },
                        ), &pattern_location
                    ),
                    expr: self.node_from_location(Expression::new(ExpressionKind::Block(BlockExpr(body))), &body_location),
                }, &start),
                self.node(MatchCase {
                    pattern: self.node(
                        Pattern::Enum(
                            EnumPattern {
                                name:
                                    self.make_access_name_from_str(
                                        "None",
                                        self.current_location()
                                    ),
                                args: AstNodes::empty(),
                            },
                        ),
                    ),
                    expr: self.node(Expression::new(ExpressionKind::Block(BlockExpr(
                        self.node(Block::Body(BodyBlock {
                            statements: ast_nodes![&self.wall; self.node(Statement::Break(BreakStatement))],
                            expr: None,
                        })),
                    )))),
                }),
            ],
        }), &start))), &start))
    }

    /// In general, a while loop transpilation process occurs by transferring the looping
    /// condition into a match block, which compares a boolean condition. If the boolean condition
    /// evaluates to false, the loop will immediately break. Otherwise the body expression is expected.
    /// A rough outline of what the transpilation process for a while loop looks like:
    ///
    /// >>> while <condition> {
    /// >>>     <block>
    /// >>> }
    /// >>>
    /// >>> // converted to
    /// >>> loop {
    /// >>>     match <condition> {
    /// >>>         true  => <block>;
    /// >>>         false => break;
    /// >>>     }
    /// >>> }
    pub fn parse_while_loop(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::While)));

        let start = self.current_location();

        self.disallow_struct_literals.set(true);
        let condition = self.parse_expression_with_precedence(0)?;
        let condition_location = condition.location();
        self.disallow_struct_literals.set(false);

        let body = self.parse_block()?;
        let body_location = body.location();

        Ok(self.node_from_joined_location(
            Block::Loop(LoopBlock(self.node_with_location(
                Block::Match(MatchBlock {
                    subject: condition,
                    cases: ast_nodes![&self.wall; self.node(MatchCase {
                            pattern: self.node(Pattern::Enum(EnumPattern {
                                name: self.make_access_name_from_str("true", body_location),
                                args: AstNodes::empty(),
                            })),
                            expr: self.node(Expression::new(ExpressionKind::Block(BlockExpr(body)))),
                        }),
                        self.node(MatchCase {
                            pattern: self.node(Pattern::Enum(EnumPattern {
                                name: self.make_access_name_from_str("false", body_location),
                                args: AstNodes::empty(),
                            })),
                            expr: self.node(Expression::new(ExpressionKind::Block(BlockExpr(
                                self.node(Block::Body(BodyBlock {
                                    statements: ast_nodes![&self.wall; self.node(Statement::Break(BreakStatement))],
                                    expr: None,
                                })),
                            )))),
                        }),
                    ],
                }),
                condition_location,
            ))),
            &start,
        ))
    }

    /// Parse a match case. A match case involves handling the pattern and the
    /// expression branch.
    pub fn parse_match_case(&self) -> AstGenResult<'c, AstNode<'c, MatchCase<'c>>> {
        let start = self.current_location();
        let pattern = self.parse_pattern()?;

        self.parse_arrow()?;
        let expr = self.parse_expression_with_precedence(0)?;

        Ok(self.node_from_joined_location(MatchCase { pattern, expr }, &start))
    }

    /// Parse a match block statement, which is composed of a subject and an arbitrary
    /// number of match cases that are surrounded in braces.
    pub fn parse_match_block(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Match)));

        let start = self.current_location();

        self.disallow_struct_literals.set(true);
        let subject = self.parse_expression_with_precedence(0)?;
        self.disallow_struct_literals.set(false);

        let mut cases = AstNodes::empty();
        // cases are wrapped in a brace tree
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            }) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, *span);

                while gen.has_token() {
                    cases.nodes.push(gen.parse_match_case()?, &self.wall);

                    gen.parse_token_atom(TokenKind::Semi)?;
                }
            }
            Some(token) => {
                let atom = token.kind;
                let expected = TokenKindVector::from_row(
                    row![&self.wall; TokenKind::Delimiter(Delimiter::Brace, true)],
                );

                self.error(AstGenErrorKind::Expected, Some(expected), Some(atom))?
            }
            _ => self.unexpected_eof()?,
        };

        Ok(self.node_from_joined_location(Block::Match(MatchBlock { subject, cases }), &start))
    }

    /// we transpile if-else blocks into match blocks in order to simplify
    /// the typechecking process and optimisation efforts.
    ///
    /// Firstly, since we always want to check each case, we convert the
    /// if statement into a series of and-patterns, where the right hand-side
    /// pattern is the condition to execute the branch...
    ///
    /// For example:
    /// >>> if a {a_branch} else if b {b_branch} else {c_branch}
    /// will be transpiled into...
    /// >>> match true {
    ///      _ if a => a_branch
    ///      _ if b => b_branch
    ///      _ => c_branch
    ///     }
    ///
    /// Additionally, if no 'else' clause is specified, we fill it with an
    /// empty block since an if-block could be assigned to any variable and therefore
    /// we need to know the outcome of all branches for typechecking.
    pub fn parse_if_statement(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        debug_assert!(matches!(
            self.current_token().kind,
            TokenKind::Keyword(Keyword::If)
        ));

        let start = self.current_location();

        let mut cases = AstNodes::empty();
        let mut has_else_branch = false;

        while self.has_token() {
            // @@Cleanup: @@Hack: essentially because struct literals begin with an ident and then a block
            //    this creates an ambiguity for the parser because it could also just be an ident
            //    and then a block, therefore, we have to peek ahead to see if we can see two following
            //    trees ('{...}') and if so, then we don't disallow parsing a struct literal, if it's
            //    only one token tree, we prevent it from being parsed as a struct literal
            //    by updating the global state...
            self.disallow_struct_literals.set(true);

            let clause = self.parse_expression_with_precedence(0)?;
            let clause_loc = clause.location();

            // We can re-enable struct literals
            self.disallow_struct_literals.set(false);

            let branch = self.parse_block()?;
            let branch_loc = branch.location();

            cases.nodes.push(
                self.node_from_location(
                    MatchCase {
                        pattern: self.node_from_location(
                            Pattern::If(IfPattern {
                                pattern: self.node_from_location(
                                    Pattern::Ignore(IgnorePattern),
                                    &clause_loc,
                                ),
                                condition: clause,
                            }),
                            &clause_loc,
                        ),
                        expr: self.node_from_location(
                            Expression::new(ExpressionKind::Block(BlockExpr(branch))),
                            &branch_loc,
                        ),
                    },
                    &clause_loc.join(branch_loc),
                ),
                &self.wall,
            );

            // Now check if there is another branch after the else or if, and loop onwards...
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Else)) => {
                    self.skip_token();

                    match self.peek() {
                        Some(token) if token.has_kind(TokenKind::Keyword(Keyword::If)) => {
                            // skip trying to convert just an 'else' branch since this is another if-branch
                            self.skip_token();
                            continue;
                        }
                        _ => (),
                    };

                    // this is the final branch of the if statement, and it is added to the end
                    // of the statements...
                    let start = self.current_location();

                    let else_branch = self.parse_block()?;
                    let loc = start.join(else_branch.location());

                    has_else_branch = true;

                    cases.nodes.push(
                        self.node_from_location(
                            MatchCase {
                                pattern: self.node(Pattern::Ignore(IgnorePattern)),
                                expr: self.node_from_location(
                                    Expression::new(ExpressionKind::Block(BlockExpr(else_branch))),
                                    &loc,
                                ),
                            },
                            &loc,
                        ),
                        &self.wall,
                    );

                    break;
                }
                _ => break,
            };
        }

        if !has_else_branch {
            cases.nodes.push(
                self.node(MatchCase {
                    pattern: self.node(Pattern::Ignore(IgnorePattern)),
                    expr: self.node(Expression::new(ExpressionKind::Block(BlockExpr(
                        self.node(Block::Body(BodyBlock {
                            statements: AstNodes::empty(),
                            expr: None,
                        })),
                    )))),
                }),
                &self.wall,
            );
        }

        Ok(self.node_from_joined_location(
            Block::Match(MatchBlock {
                subject: self.make_ident("true", &self.current_location()),
                cases,
            }),
            &start,
        ))
    }

    /// Function to parse a fat arrow component '=>' in any given context.
    fn parse_arrow(&self) -> AstGenResult<'c, ()> {
        let current_location = self.current_location();

        // Essentially, we want to re-map the error into a more concise one given
        // the parsing context.
        if self.parse_token_atom(TokenKind::Eq).is_err() {
            return self.error_with_location(
                AstGenErrorKind::ExpectedArrow,
                None,
                None,
                &current_location,
            )?;
        }

        if self.parse_token_atom(TokenKind::Gt).is_err() {
            return self.error_with_location(
                AstGenErrorKind::ExpectedArrow,
                None,
                None,
                &current_location,
            )?;
        }

        Ok(())
    }

    /// Parse a let declaration statement.
    ///
    /// Let statement parser which parses three possible variations. The let keyword
    /// is parsed and then either a variable declaration, function declaration, or both.
    /// As such a name is returned before parsing a type, function, or both.
    /// Let keyword statement, a destructuring pattern, potential for-all statement, optional
    /// type definition and a potential definition of the right hand side. For example:
    /// ```text
    /// let some_var...<int>: float = ...;
    ///     ^^^^^^^^   ^^^^^  ^^^^^   ^^^─────┐
    ///    pattern     bound   type    the right hand-side expr
    /// ```
    pub fn parse_let_statement(&self) -> AstGenResult<'c, LetStatement<'c>> {
        debug_assert!(matches!(
            self.current_token().kind,
            TokenKind::Keyword(Keyword::Let)
        ));

        let pattern = self.parse_pattern()?;

        let bound = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Lt) => Some(self.parse_type_bound()?),
            _ => None,
        };

        let ty = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Colon) => {
                self.skip_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        let value = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Eq) => {
                self.skip_token();
                Some(self.parse_expression_with_precedence(0)?)
            }
            _ => None,
        };

        Ok(LetStatement {
            pattern,
            ty,
            bound,
            value,
        })
    }

    /// Parse a pattern collect which can involve an arbitrary number of patterns which
    /// are comma separated.
    pub fn parse_pattern_collection(
        &self,
        tree: &'stream Row<'stream, Token>,
        span: Location,
    ) -> AstGenResult<'c, AstNodes<'c, Pattern<'c>>> {
        let gen = self.from_stream(tree, span);

        gen.parse_separated_fn(
            || gen.parse_pattern(),
            || gen.parse_token_atom(TokenKind::Comma),
        )
    }

    /// Parse a destructuring pattern. The destructuring pattern refers to destructuring
    /// either a struct or a namespace to extract fields, exported members. The function
    /// takes in a token atom because both syntaxes use different operators as pattern
    /// assigners.
    pub fn parse_destructuring_pattern(
        &self,
    ) -> AstGenResult<'c, AstNode<'c, DestructuringPattern<'c>>> {
        let start = self.current_location();
        let name = self.parse_ident()?;

        // if the next token is the correct assigning operator, attempt to parse a
        // pattern here, if not then we copy the parsed ident and make a binding
        // pattern.
        let pattern = match self.peek_resultant_fn(|| self.parse_token_atom(TokenKind::Eq)) {
            Some(_) => self.parse_pattern()?,
            None => {
                let copy = self.node(Name { ..*name.body() });
                let loc = copy.location();
                self.node_with_location(Pattern::Binding(BindingPattern(copy)), loc)
            }
        };

        Ok(self.node_from_joined_location(DestructuringPattern { name, pattern }, &start))
    }

    /// Parse a collection of destructuring patterns that are comma separated.
    pub fn parse_destructuring_patterns(
        &self,
        tree: &'stream Row<'stream, Token>,
        span: Location,
    ) -> AstGenResult<'c, AstNodes<'c, DestructuringPattern<'c>>> {
        let gen = self.from_stream(tree, span);

        let mut patterns = AstNodes::new(row![&self.wall;], Some(span));

        while gen.has_token() {
            match gen.peek_resultant_fn(|| gen.parse_destructuring_pattern()) {
                Some(pat) => patterns.nodes.push(pat, &self.wall),
                None => break,
            }

            if gen.has_token() {
                gen.parse_token_atom(TokenKind::Comma)?;
            }
        }

        Ok(patterns)
    }

    /// Parse a singular pattern. Singular patterns cannot have any grouped pattern
    /// operators such as a '|', if guards or any form of compound pattern.
    pub fn parse_singular_pattern(&self) -> AstGenResult<'c, AstNode<'c, Pattern<'c>>> {
        let token = self.peek();

        if token.is_none() {
            return self.unexpected_eof()?;
        }

        let token = token.unwrap();
        let start = token.span;

        let pattern = match token {
            Token {
                kind: TokenKind::Ident(ident),
                span,
            } => {
                // this could be either just a binding pattern, enum, or a struct pattern
                self.skip_token();

                // So here we try to parse an access name, if it is only made of a single binding
                // name, we'll just return this as a binding pattern, otherwise it must follow that
                // it is either a enum or struct pattern, if not we report it as an error since
                // access names cannot be used as binding patterns on their own...
                let name = self.parse_access_name(ident)?;

                match self.peek() {
                    // Destructuring pattern for either struct or namespace
                    Some(Token {
                        kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                        span,
                    }) => {
                        self.skip_token();
                        let tree = self.token_trees.get(*tree_index).unwrap();

                        Pattern::Struct(StructPattern {
                            name,
                            entries: self.parse_destructuring_patterns(tree, *span)?,
                        })
                    }
                    // enum_pattern
                    Some(Token {
                        kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                        span,
                    }) => {
                        self.skip_token();
                        let tree = self.token_trees.get(*tree_index).unwrap();

                        Pattern::Enum(EnumPattern {
                            name,
                            args: self.parse_pattern_collection(tree, *span)?,
                        })
                    }
                    Some(token) if name.path.len() > 1 => self.error(
                        AstGenErrorKind::Expected,
                        Some(TokenKindVector::begin_pattern_collection(&self.wall)),
                        Some(token.kind),
                    )?,
                    _ => {
                        if *ident == CORE_IDENTIFIERS.underscore {
                            Pattern::Ignore(IgnorePattern)
                        } else {
                            Pattern::Binding(BindingPattern(
                                self.node_from_location(Name { ident: *ident }, span),
                            ))
                        }
                    }
                }
            }
            token if token.kind.is_literal() => {
                self.skip_token();
                Pattern::Literal(self.convert_literal_kind_into_pattern(&token.kind))
            }
            Token {
                kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                span,
            } => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();

                // check here if the tree length is 1, and the first token is the comma to check if it is an
                // empty tuple pattern...
                if let Some(token) = tree.get(0) {
                    if token.has_kind(TokenKind::Comma) {
                        return Ok(self.node_from_location(
                            Pattern::Tuple(TuplePattern {
                                elements: AstNodes::empty(),
                            }),
                            span,
                        ));
                    }
                }

                // @@Hack: here it might actually be a nested pattern in parenthesees. So we perform a slight
                // transformation if the number of parsed patterns is only one. So essentially we handle the case
                // where a pattern is wrapped in parentheses and so we just unwrap it.
                let mut elements = self.parse_pattern_collection(tree, *span)?;

                if elements.len() == 1 {
                    let element = elements.nodes.pop().unwrap();
                    return Ok(element);
                } else {
                    Pattern::Tuple(TuplePattern { elements })
                }
            }
            Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            } => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();

                Pattern::Namespace(NamespacePattern {
                    patterns: self.parse_destructuring_patterns(tree, *span)?,
                })
            }
            // @@Future: List patterns aren't supported yet.
            // Token {kind: TokenKind::Tree(Delimiter::Bracket, tree), span} => {
            //                 self.skip_token();
            //     // this is a list pattern
            //
            // }
            token => self.error_with_location(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::begin_pattern(&self.wall)),
                Some(token.kind),
                &token.span,
            )?,
        };

        Ok(self.node_from_joined_location(pattern, &start))
    }

    /// Parse a block.
    pub fn parse_block(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        let (gen, start) = match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            }) => {
                self.skip_token(); // step-along since we matched a block...

                let tree = self.token_trees.get(*tree_index).unwrap();

                (self.from_stream(tree, self.current_location()), *span)
            }
            Some(token) => self.error(AstGenErrorKind::Block, None, Some(token.kind))?,
            // @@ErrorReporting
            None => {
                self.error_with_location(AstGenErrorKind::Block, None, None, &self.next_location())?
            }
        };

        self.parse_block_from_gen(&gen, start, None)
    }

    /// Function to parse a block body
    pub fn parse_block_from_gen(
        &self,
        gen: &Self,
        start: Location,
        initial_statement: Option<AstNode<'c, Statement<'c>>>,
    ) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        // Edge case where the statement is parsed and the 'last_statement_is_expr' is set, here
        // we take the expression and return a block that has the expression left here.

        // Append the initial statement if there is one.
        let mut block = if initial_statement.is_some() {
            BodyBlock {
                statements: ast_nodes![&self.wall; initial_statement.unwrap()],
                expr: None,
            }
        } else {
            BodyBlock {
                statements: AstNodes::empty(),
                expr: None,
            }
        };

        // Just return an empty block if we don't get anything
        if !gen.has_token() {
            return Ok(self.node_with_location(Block::Body(block), start));
        }

        // firstly check if the first token signals a beginning of a statement, we can tell
        // this by checking for keywords that must begin a statement...
        while gen.has_token() {
            let token = gen.peek().unwrap();

            if token.kind.begins_statement() {
                block
                    .statements
                    .nodes
                    .push(gen.parse_statement()?, &self.wall);
                continue;
            }

            // if we can't tell if this is a statement, we parse an expression, and if there
            // is a following semi-colon, then we make this a statement and continue...
            let expr = gen.parse_expression_with_precedence(0)?;
            let expr_loc = expr.location();

            // check for assigning operators here if the lhs expression is not compound
            match gen.peek_resultant_fn(|| gen.parse_re_assignment_op()) {
                Some(op) => {
                    // since this is followed by an expression, we try to parse another expression, and then
                    // ensure that after an expression there is a ending semi colon.
                    let rhs = gen.parse_expression_with_precedence(0)?;
                    gen.parse_token_atom(TokenKind::Semi)?;

                    block.statements.nodes.push(
                        gen.node_from_joined_location(
                            Statement::Expr(ExprStatement(
                                self.transform_binary_expression(expr, rhs, op),
                            )),
                            &expr_loc,
                        ),
                        &self.wall,
                    );
                }
                None => {
                    match gen.peek() {
                        Some(token) if token.has_kind(TokenKind::Semi) => {
                            gen.skip_token();

                            block.statements.nodes.push(
                                gen.node_from_joined_location(
                                    Statement::Expr(ExprStatement(expr)),
                                    &expr_loc,
                                ),
                                &self.wall,
                            );
                        }
                        Some(token) if token.has_kind(TokenKind::Eq) => {
                            gen.skip_token();

                            // Parse the rhs and the semi
                            let rhs = gen.parse_expression_with_precedence(0)?;
                            gen.parse_token_atom(TokenKind::Semi)?;

                            block.statements.nodes.push(
                                gen.node_from_joined_location(
                                    Statement::Assign(AssignStatement { lhs: expr, rhs }),
                                    &start,
                                ),
                                &self.wall,
                            );
                        }
                        Some(token) => {
                            match expr.into_body().move_out().into_kind() {
                                ExpressionKind::Block(BlockExpr(inner_block)) => {
                                    block.statements.nodes.push(
                                        gen.node_from_joined_location(
                                            Statement::Block(BlockStatement(inner_block)),
                                            &expr_loc,
                                        ),
                                        &self.wall,
                                    )
                                }
                                _ => gen.error(
                                    AstGenErrorKind::Expected,
                                    Some(TokenKindVector::from_row(
                                        row![&self.wall; TokenKind::Semi],
                                    )),
                                    Some(token.kind),
                                )?,
                            };
                        }
                        None => {
                            block.expr = Some(expr);
                            break;
                        }
                    };
                }
            }
        }

        Ok(self.node_from_joined_location(Block::Body(block), &start))
    }

    /// Parse an expression which can be compound.
    pub fn parse_expression(&self) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let token = self.next_token();

        if token.is_none() {
            return self.unexpected_eof()?;
        }

        let prev_allowance = self.disallow_struct_literals.get();
        let token = token.unwrap();

        // ::CompoundExpressions: firstly, we have to get the initial part of the expression, and then we can check
        // if there are any additional parts in the forms of either property accesses, indexing or infix function calls
        let subject = match &token.kind {
            kind if kind.is_unary_op() => return self.parse_unary_expression(),

            // Handle primitive literals
            kind if kind.is_literal() => self.parse_literal(),
            TokenKind::Ident(ident) => {
                // record the starting span
                let start = self.current_location();

                let (name, type_args) = self.parse_name_with_type_args(ident)?;
                let type_args = type_args.unwrap_or_else(AstNodes::empty);

                // create the lhs expr.
                self.node_with_location(
                    Expression::new(ExpressionKind::Variable(VariableExpr { name, type_args })),
                    start.join(self.current_location()),
                )
            }

            // @@Note: This doesn't cover '{' case.
            kind if kind.begins_block() => {
                let start = self.current_location();

                let block = match kind {
                    TokenKind::Keyword(Keyword::For) => self.parse_for_loop()?,
                    TokenKind::Keyword(Keyword::While) => self.parse_while_loop()?,
                    TokenKind::Keyword(Keyword::Loop) => self.node_from_joined_location(
                        Block::Loop(LoopBlock(self.parse_block()?)),
                        &start,
                    ),
                    TokenKind::Keyword(Keyword::If) => self.parse_if_statement()?,
                    TokenKind::Keyword(Keyword::Match) => self.parse_match_block()?,
                    _ => unreachable!(),
                };

                self.node_from_joined_location(
                    Expression::new(ExpressionKind::Block(BlockExpr(block))),
                    &start,
                )
            }
            // Import
            TokenKind::Keyword(Keyword::Import) => self.parse_import()?,
            // Handle tree literals
            TokenKind::Tree(Delimiter::Brace, tree_index) => {
                let tree = self.token_trees.get(*tree_index).unwrap();

                self.parse_block_or_braced_literal(tree, &self.current_location())?
            }
            TokenKind::Tree(Delimiter::Bracket, tree_index) => {
                let tree = self.token_trees.get(*tree_index).unwrap();

                self.parse_array_literal(tree, &self.current_location())?
            }
            TokenKind::Tree(Delimiter::Paren, tree_index) => {
                self.disallow_struct_literals.set(true); // @@Cleanup

                // check whether a function return type is following...
                let mut is_func =
                    matches!(self.peek(), Some(token) if token.has_kind(TokenKind::Colon));

                // Now here we have to look ahead after the token_tree to see if there is an arrow
                if !is_func {
                    // @@Speed: avoid using parse_token_atom() because we don't care about error messages
                    //          We just want to purely look if there are is a combination of symbols following
                    //          which make up an '=>'.
                    let has_arrow = self
                        .peek_resultant_fn(|| -> Result<(), ()> {
                            self.parse_token_atom_fast(TokenKind::Eq).ok_or(())?;
                            self.parse_token_atom_fast(TokenKind::Gt).ok_or(())?;
                            Ok(())
                        })
                        .is_some();

                    if has_arrow {
                        self.offset.set(self.offset.get() - 2);
                        is_func = true;
                    }
                }

                let tree = self.token_trees.get(*tree_index).unwrap();

                match is_func {
                    true => {
                        let gen = self.from_stream(tree, token.span);
                        self.parse_function_literal(&gen)?
                    }
                    false => self.parse_expression_or_tuple(tree, &self.current_location())?,
                }
            }

            kind @ TokenKind::Keyword(_) => {
                return self.error_with_location(
                    AstGenErrorKind::Keyword,
                    None,
                    Some(*kind),
                    &token.span,
                )
            }
            kind => {
                return self.error_with_location(
                    AstGenErrorKind::ExpectedExpression,
                    None,
                    Some(*kind),
                    &token.span,
                )
            }
        };

        // reset the struct literal state in any case
        self.disallow_struct_literals.set(prev_allowance);

        self.parse_singular_expression(subject)
    }

    /// Provided an initial subject expression that is parsed by the parent caller, this function
    /// will check if there are any additional components to the expression; in the form of either
    /// property access, infix function calls, indexing, etc.
    pub fn parse_singular_expression(
        &self,
        subject: AstNode<'c, Expression<'c>>,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        // record the starting span
        let start = self.current_location();

        let mut lhs_expr = subject;

        // so here we need to peek to see if this is either a index_access, field access or a function call...
        while let Some(next_token) = self.peek() {
            match &next_token.kind {
                // Property access or infix function call
                TokenKind::Dot => {
                    self.skip_token(); // eat the token since there isn't any alternative to being an ident or fn call.

                    let name_or_fn_call = self.parse_name_or_infix_call()?;
                    let kind = name_or_fn_call.into_body().move_out().into_kind();

                    match kind {
                        ExpressionKind::FunctionCall(FunctionCallExpr { subject, mut args }) => {
                            // @@Future: ##FunctionArguments:
                            // In the future when we consider function named arguments and optional arguments and variadic arguments,
                            // is it correct to apply the same behaviour of placing the argument first if it is an infix call ?
                            // The current behaviour is that the lhs is inserted as the first argument, but that might change:
                            //
                            // >>> foo.bar()
                            // vvv Is transpiled to..
                            // >>> bar(foo)
                            //
                            // Additionally, if the RHS has arguments, they are shifted for the LHS to be inserted as the first argument...
                            //
                            // >>> foo.bar(baz)
                            // vvv Is transpiled to..
                            // >>> bar(foo, baz)

                            // insert lhs_expr first...
                            args.entries.nodes.insert(0, lhs_expr, &self.wall);

                            lhs_expr = self.node_from_joined_location(
                                Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                                    subject,
                                    args,
                                })),
                                &start,
                            );
                        }
                        ExpressionKind::Variable(VariableExpr { name, type_args: _ }) => {
                            // @@Cleanup: This produces an AstNode<AccessName> whereas we just want the single name...
                            let location = name.location();
                            let ident = name.body().path.get(0).unwrap();

                            let node = self.node_with_location(Name { ident: *ident }, location);

                            lhs_expr = self.node_with_location(
                                Expression::new(ExpressionKind::PropertyAccess(
                                    PropertyAccessExpr {
                                        subject: lhs_expr,
                                        property: node,
                                    },
                                )),
                                location,
                            );
                        }
                        _ => self.error(AstGenErrorKind::InfixCall, None, None)?,
                    }
                }
                // Array index access syntax: ident[...]
                TokenKind::Tree(Delimiter::Bracket, tree_index) => {
                    self.skip_token();

                    let tree = self.token_trees.get(*tree_index).unwrap();
                    lhs_expr = self.parse_array_index(lhs_expr, tree, self.current_location())?;
                }
                // Function call
                TokenKind::Tree(Delimiter::Paren, tree_index) => {
                    self.skip_token();

                    let tree = self.token_trees.get(*tree_index).unwrap();
                    lhs_expr = self.parse_function_call(lhs_expr, tree, self.current_location())?;
                }
                // Struct literal
                TokenKind::Tree(Delimiter::Brace, tree_index)
                    if !self.disallow_struct_literals.get() =>
                {
                    // Ensure that the LHS of the brace is a variable, since struct literals can only
                    // be begun with variable names and type arguments, any other expression cannot be
                    // the beginning of a struct literal.
                    let location = lhs_expr.location();
                    let mut break_now = false;

                    lhs_expr = match lhs_expr.into_body().move_out().into_kind() {
                        ExpressionKind::Variable(VariableExpr { name, type_args }) => {
                            self.skip_token();

                            let tree = self.token_trees.get(*tree_index).unwrap();
                            self.parse_struct_literal(name, type_args, tree)?
                        }
                        expr => {
                            break_now = true;
                            self.node_with_location(Expression::new(expr), location)
                        }
                    };

                    if break_now {
                        break;
                    }
                }
                _ => break,
            }
        }

        Ok(lhs_expr)
    }

    /// Parsing module import statement which are in the form of a function
    /// call that have a single argument in the form of a string literal.
    /// The syntax is as follows:
    ///
    /// import("./relative/path/to/module")
    ///
    /// The path argument to imports automatically assumes that the path you provide
    /// is references '.hash' extension file or a directory with a 'index.hash' file
    /// contained within the directory.
    pub fn parse_import(&self) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let pre = self.current_token().span;
        let start = self.current_location();

        let (tree, span) = match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                span,
            }) => {
                let tree = self.token_trees.get(*tree_index).unwrap();
                (tree, *span)
            }
            Some(token) => self.error(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::from_row(
                    row![&self.wall; TokenKind::Delimiter(Delimiter::Paren, true)],
                )),
                Some(token.kind),
            )?,
            None => self.unexpected_eof()?,
        };

        let gen = self.from_stream(tree, span);

        let (raw, path, span) = match gen.peek() {
            Some(Token {
                kind: TokenKind::StrLiteral(str),
                span,
            }) => (str, STRING_LITERAL_MAP.lookup(*str), span),
            _ => gen.error(AstGenErrorKind::ImportPath, None, None)?,
        };

        gen.skip_token(); // eat the string argument

        if gen.has_token() {
            gen.expected_eof()?;
        }

        // Attempt to add the module via the resolver
        let import_path = PathBuf::from_str(path).unwrap_or_else(|err| match err {});
        let resolved_import_path = self
            .resolver
            .parse_import(&import_path, self.source_location(span));

        match resolved_import_path {
            Ok(resolved_import_path) => Ok(self.node_from_joined_location(
                Expression::new(ExpressionKind::Import(ImportExpr(
                    self.node_from_joined_location(
                        Import {
                            path: *raw,
                            resolved_path: resolved_import_path,
                        },
                        &start,
                    ),
                ))),
                &start,
            )),
            Err(err) => self.error_with_location(
                AstGenErrorKind::ErroneousImport(err),
                None,
                None,
                &pre.join(self.current_location()),
            ),
        }
    }

    /// Parse a function call which requires that the [AccessName] is pre-parsed and passed
    /// into the function which deals with the call arguments.
    pub fn parse_function_call(
        &self,
        ident: AstNode<'c, Expression<'c>>,
        tree: &'stream Row<'stream, Token>,
        span: Location,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, span);
        let mut args = AstNode::new(
            FunctionCallArgs {
                entries: AstNodes::empty(),
            },
            span,
            &self.wall,
        );

        while gen.has_token() {
            let arg = gen.parse_expression_with_precedence(0);
            args.entries.nodes.push(arg?, &self.wall);

            // now we eat the next token, checking that it is a comma
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => gen.next_token(),
                _ => break,
            };
        }

        // form the span from the beginning variable expression to the end of the arguments...
        let span = &ident.location().join(self.current_location());

        Ok(self.node_with_location(
            Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                subject: ident,
                args,
            })),
            *span,
        ))
    }

    /// Function to parse a token atom optionally. If the appropriate token atom is
    /// present we advance the token count, if not then just return None
    pub fn parse_token_atom_fast(&self, atom: TokenKind) -> Option<()> {
        match self.peek() {
            Some(token) if token.has_kind(atom) => {
                self.skip_token();
                Some(())
            }
            _ => None,
        }
    }

    /// Function to parse the next token with the same kind as the specified kind, this
    /// is a useful utility function for parsing singular tokens in the place of more complex
    /// compound statements and expressions.
    pub fn parse_token_atom(&self, atom: TokenKind) -> AstGenResult<'c, ()> {
        match self.peek() {
            Some(token) if token.has_kind(atom) => {
                self.skip_token();
                Ok(())
            }
            Some(token) => self.error_with_location(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::singleton(&self.wall, atom)),
                Some(token.kind),
                &token.span,
            ),
            _ => self.error(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::singleton(&self.wall, atom)),
                None,
            ),
        }
    }

    /// Parse a struct literal.
    pub fn parse_struct_literal(
        &self,
        name: AstNode<'c, AccessName<'c>>,
        type_args: AstNodes<'c, Type<'c>>,
        tree: &'stream Row<'stream, Token>,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let start = self.current_location();
        let gen = self.from_stream(tree, start);

        let mut entries = AstNodes::empty();

        while gen.has_token() {
            let name = gen.parse_ident()?;
            let location = name.location();

            // we want to support the syntax where we can just assign a struct field that has
            // the same name as a variable in scope. For example, if you were to create a
            // struct like so:
            //
            // >>> let name = "Viktor";
            // >>> let dog = Dog { name };
            //
            // This should be de-sugared into:
            //
            // ...
            // >>> let dog = Dog { name = name };
            //
            // So, here we handle for this case...
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Eq) => {
                    gen.skip_token();

                    let value = gen.parse_expression_with_precedence(0)?;

                    entries.nodes.push(
                        gen.node_with_location(
                            StructLiteralEntry { name, value },
                            location.join(gen.current_location()),
                        ),
                        &self.wall,
                    );

                    // now we eat the next token, checking that it is a comma
                    match gen.peek() {
                        Some(token) if token.has_kind(TokenKind::Comma) => gen.skip_token(),
                        _ => break,
                    };
                }
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    gen.skip_token();

                    // we need to copy the name node and make it into a new expression with the same span
                    let name_copy = gen.make_variable_from_identifier(name.ident, name.location());

                    entries.nodes.push(
                        gen.node_with_location(
                            StructLiteralEntry {
                                name,
                                value: name_copy,
                            },
                            location.join(gen.current_location()),
                        ),
                        &self.wall,
                    );
                }
                None => {
                    // we need to copy the name node and make it into a new expression with the same span
                    let name_copy = gen.make_variable_from_identifier(name.ident, name.location());

                    entries.nodes.push(
                        gen.node_with_location(
                            StructLiteralEntry {
                                name,
                                value: name_copy,
                            },
                            location.join(gen.current_location()),
                        ),
                        &self.wall,
                    );

                    break;
                }
                Some(token) => gen.error_with_location(
                    AstGenErrorKind::Expected,
                    Some(TokenKindVector::from_row(
                        row![&self.wall; TokenKind::Eq, TokenKind::Comma],
                    )),
                    Some(token.kind),
                    &token.span,
                )?,
            }
        }

        Ok(self.node_from_joined_location(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                self.node_from_joined_location(
                    Literal::Struct(StructLiteral {
                        name,
                        type_args,
                        entries,
                    }),
                    &start,
                ),
            ))),
            &start,
        ))
    }

    /// Parse an array index. Array indexes are constructed with square brackets
    /// wrapping a singular expression.
    pub fn parse_array_index(
        &self,
        ident: AstNode<'c, Expression<'c>>,
        tree: &'stream Row<'stream, Token>,
        span: Location,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, span);
        let start = gen.current_location();

        // parse the indexing expression between the square brackets...
        let index_expr = gen.parse_expression_with_precedence(0)?;
        let index_loc = index_expr.location();

        // since nothing should be after the expression, we can check that no tokens
        // are left and the generator is empty, otherwise report this as an unexpected_token
        if gen.has_token() {
            gen.expected_eof()?;
        }

        Ok(self.node_with_location(
            Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                subject: self.make_ident("index", &start),
                args: self.node_with_location(
                    FunctionCallArgs {
                        entries: ast_nodes![&self.wall; ident, index_expr],
                    },
                    index_loc,
                ),
            })),
            gen.current_location(),
        ))
    }

    /// Parses a unary operator followed by a singular expression. Once the unary operator
    /// is picked up, the expression is transformed into a function call to the corresponding
    /// trait that implements the unary operator operation.
    pub fn parse_unary_expression(&self) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let token = self.current_token();
        let start = self.current_location();

        let expr_kind = match &token.kind {
            TokenKind::Star => ExpressionKind::Deref(DerefExpr(self.parse_expression()?)),
            TokenKind::Amp => {
                // Check if this reference is raw...
                match self.peek() {
                    Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Raw)) => {
                        self.skip_token();
                        ExpressionKind::Ref(RefExpr {
                            inner_expr: self.parse_expression()?,
                            kind: RefKind::Raw,
                        })
                    }
                    _ => ExpressionKind::Ref(RefExpr {
                        inner_expr: self.parse_expression()?,
                        kind: RefKind::Normal,
                    }),
                }
            }
            kind @ (TokenKind::Plus | TokenKind::Minus) => {
                let expr = self.parse_expression()?;
                let loc = expr.location();

                let fn_name = match kind {
                    TokenKind::Plus => "pos",
                    TokenKind::Minus => "neg",
                    _ => unreachable!(),
                };

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident(fn_name, &start),
                    args: self.node_from_location(
                        FunctionCallArgs {
                            entries: ast_nodes![&self.wall; expr],
                        },
                        &loc,
                    ),
                })
            }
            TokenKind::Tilde => {
                let arg = self.parse_expression()?;
                let loc = arg.location();

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident("notb", &start),
                    args: self.node_from_location(
                        FunctionCallArgs {
                            entries: ast_nodes![&self.wall; arg],
                        },
                        &loc,
                    ),
                })
            }
            TokenKind::Hash => {
                // First get the intrinsic subject, and expect a possible singular expression
                // followed by the intrinsic.
                let subject = self.parse_ident()?;
                let name = subject.ident;

                // create the subject node
                let subject_node = self.node_from_joined_location(
                    Expression::new(ExpressionKind::Intrinsic(IntrinsicKey { name })),
                    &start,
                );

                return self.parse_singular_expression(subject_node);
            }
            TokenKind::Exclamation => {
                let arg = self.parse_expression()?;
                let loc = arg.location();

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident("not", &start),
                    args: self.node_from_location(
                        FunctionCallArgs {
                            entries: ast_nodes![&self.wall; arg],
                        },
                        &loc,
                    ),
                })
            }
            kind => panic!("Expected token to be a unary operator, but got '{}'", kind),
        };

        Ok(self.node_from_joined_location(Expression::new(expr_kind), &start))
    }

    /// Parse a trait bound.
    pub fn parse_trait_bound(
        &self,
        ident: &Identifier,
    ) -> AstGenResult<'c, (AstNode<'c, AccessName<'c>>, AstNodes<'c, Type<'c>>)> {
        let name = self.parse_access_name(ident)?;
        let args = self.parse_type_args()?;

        Ok((name, args))
    }

    /// Parse an access name followed by optional type arguments..
    pub fn parse_name_with_type_args(
        &self,
        ident: &Identifier,
    ) -> AstGenResult<'c, (AstNode<'c, AccessName<'c>>, Option<AstNodes<'c, Type<'c>>>)> {
        let name = self.parse_access_name(ident)?;

        // @@Speed: so here we want to be efficient about type_args, we'll just try to
        // see if the next token atom is a 'Lt' rather than using parse_token_atom
        // because it throws an error essentially and thus allocates a stupid amount
        // of strings which at the end of the day aren't even used...
        let args = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Lt) => {
                self.peek_resultant_fn(|| self.parse_type_args())
            }
            _ => None,
        };

        Ok((name, args))
    }

    /// Parses a single identifier, essentially converting the current [TokenKind::Ident] into
    /// an [AstNode<Name>], assuming that the next token is an identifier.
    pub fn parse_ident(&self) -> AstGenResult<'c, AstNode<'c, Name>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Ident(ident),
                span,
            }) => {
                self.skip_token();

                Ok(AstNode::new(Name { ident: *ident }, *span, &self.wall))
            }
            Some(token) => self.error_with_location(
                AstGenErrorKind::ExpectedIdentifier,
                None,
                Some(token.kind),
                &token.span,
            ),
            None => self.unexpected_eof(),
        }
    }

    /// Parse an [AccessName] from the current token stream. An [AccessName] is defined as
    /// a number of identifiers that are separated by the namespace operator '::'. The function
    /// presumes that the current token is an identifier an that the next token is a colon.
    pub fn parse_access_name(
        &self,
        start_id: &Identifier,
    ) -> AstGenResult<'c, AstNode<'c, AccessName<'c>>> {
        let start = self.current_location();
        let mut path = row![&self.wall; *start_id];

        loop {
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Colon) => {
                    self.skip_token(); // :

                    match self.peek() {
                        Some(token) if token.has_kind(TokenKind::Colon) => {
                            self.skip_token(); // :

                            match self.peek() {
                                Some(Token {
                                    kind: TokenKind::Ident(id),
                                    span: _,
                                }) => {
                                    self.skip_token();
                                    path.push(*id, &self.wall);
                                }
                                _ => self.error(AstGenErrorKind::AccessName, None, None)?,
                            }
                        }
                        _ => {
                            // backtrack the token count by one
                            self.offset.set(self.offset() - 1);
                            break;
                        }
                    }
                }
                _ => break,
            }
        }

        Ok(AstNode::new(
            AccessName { path },
            start.join(self.current_location()),
            &self.wall,
        ))
    }

    /// Special variant of expression to handle interactive statements that have relaxed rules about
    /// semi-colons for some statements.
    pub fn generate_expression_from_interactive(
        &mut self,
    ) -> AstGenResult<'c, AstNode<'c, BodyBlock<'c>>> {
        Ok(AstNode::new(
            BodyBlock {
                statements: AstNodes::empty(),
                expr: None,
            },
            Location::span(0, 0),
            &self.wall,
        ))
    }

    /// Parse an expression whilst taking into account binary precedence operators.
    /// Parse chain of expressions with chain links being binary operators. Whilst
    /// parsing the chain, figure out the applicative precedence of each operator using
    /// Pratt parsing.
    pub fn parse_expression_with_precedence(
        &self,
        mut min_prec: u8,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        // first of all, we want to get the lhs...
        let mut lhs = self.parse_expression()?;

        // reset the compound_expr flag, since this is a new expression...
        self.is_compound_expr.set(false);

        loop {
            let op_start = self.next_location();
            // this doesn't consider operators that have an 'eq' variant because that is handled at the statement level,
            // since it isn't really a binary operator...
            let (op, consumed_tokens) = self.parse_operator();

            match op {
                // check if the operator here is re-assignable, as in '+=', '/=', if so then we need to stop
                // parsing onwards because this might be an assignable expression...
                // Only perform this check if know prior that the expression is not made of compounded components.
                Some(op) if !op.assignable => {
                    // consume the number of tokens eaten whilst getting the operator...
                    self.offset.update(|x| x + consumed_tokens as usize);

                    let op_span = op_start.join(self.current_location());

                    // check if we have higher precedence than the lhs expression...
                    let (l_prec, r_prec) = op.kind.infix_binding_power();

                    if l_prec < min_prec {
                        self.offset.update(|x| x - consumed_tokens as usize);
                        break;
                    }

                    // if the operator is a non-functional, (e.g. as) we need to perform a different conversion
                    // where we transform the AstNode into a different
                    if matches!(op.kind, OperatorKind::As) {
                        lhs = self.node_from_joined_location(
                            Expression::new(ExpressionKind::Typed(TypedExpr {
                                expr: lhs,
                                ty: self.parse_type()?,
                            })),
                            &op_span,
                        );

                        // since we don't descend, we still need to update the precedence to
                        // being 'r_prec'.
                        min_prec = r_prec;
                    } else {
                        let rhs = self.parse_expression_with_precedence(r_prec)?;
                        self.is_compound_expr.set(true);

                        // transform the operator into an OperatorFn
                        lhs = self.transform_binary_expression(
                            lhs,
                            rhs,
                            self.node_with_location(op, op_span),
                        );
                    }
                }
                _ => break,
            }
        }

        Ok(lhs)
    }

    /// This parses some type args after an [AccessName], however due to the nature of the
    /// language grammar, since the [TokenKind] could be a `TokenKind::Lt` or `<`, it could
    /// also be a comparison rather than the beginning of a type argument. Therefore, we have to
    /// lookahead to see if there is another type followed by either a comma (which locks the
    /// type_args) or a closing `TokenKind::Gt`. Otherwise, we back track and let the expression
    /// be parsed as an order comparison.
    pub fn parse_type_args(&self) -> AstGenResult<'c, AstNodes<'c, Type<'c>>> {
        self.parse_token_atom(TokenKind::Lt)?;
        let mut type_args = AstNodes::empty();

        loop {
            // Check if the type argument is parsed, if we have already encountered a comma, we
            // return a hard error because it has already started on a comma.
            match self.parse_type() {
                Ok(ty) => type_args.nodes.push(ty, &self.wall),
                Err(err) => return Err(err),
            };

            // Now consider if the bound is closing or continuing with a comma...
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    self.skip_token();
                }
                Some(token) if token.has_kind(TokenKind::Gt) => {
                    self.skip_token();
                    break;
                }
                Some(token) => self.error(
                    AstGenErrorKind::Expected,
                    Some(TokenKindVector::from_row(
                        row![&self.wall; TokenKind::Comma, TokenKind::Gt],
                    )),
                    Some(token.kind),
                )?,
                None => self.unexpected_eof()?,
            }
        }

        Ok(type_args)
    }

    /// Parses a function type which involves a parenthesis token tree with some arbitrary
    /// number of comma separated types followed by a return type that is preceded by an
    /// arrow after the parentheses.
    ///
    ///  (e.g. (i32) => str)
    ///
    pub fn parse_function_or_tuple_type(
        &self,
        must_be_function: bool,
    ) -> AstGenResult<'c, AstNode<'c, Type<'c>>> {
        let start = self.current_location();

        let mut type_args = AstNodes::empty();

        // handle the function arguments first by checking for parentheses
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                span,
            }) => {
                self.skip_token();

                // update the type argument span...
                type_args.span = Some(*span);

                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, *span);

                match gen.peek() {
                    // Handle special case where there is only one comma and no following items...
                    // Special edge case for '(,)' or an empty tuple type...
                    Some(token) if token.has_kind(TokenKind::Comma) && gen.stream.len() == 1 => {
                        gen.skip_token();
                    }
                    _ => {
                        type_args = gen.parse_separated_fn(
                            || gen.parse_type(),
                            || gen.parse_token_atom(TokenKind::Comma),
                        )?;
                    }
                };
            }
            Some(token) => self.error(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::from_row(
                    row![&self.wall; TokenKind::Delimiter(Delimiter::Paren, false)],
                )),
                Some(token.kind),
            )?,
            None => self.unexpected_eof()?,
        };

        // If there is an arrow '=>', then this must be a function type
        let name = match self.peek_resultant_fn(|| self.parse_arrow()) {
            Some(_) => {
                // Parse the return type here, and then give the function name
                type_args.nodes.push(self.parse_type()?, &self.wall);
                IDENTIFIER_MAP.create_ident(FUNCTION_TYPE_NAME)
            }
            None => {
                if must_be_function {
                    self.error(AstGenErrorKind::ExpectedFnArrow, None, None)?;
                }

                IDENTIFIER_MAP.create_ident(TUPLE_TYPE_NAME)
            }
        };

        Ok(self.node_from_joined_location(
            Type::Named(NamedType {
                name: self
                    .make_access_name_from_identifier(name, start.join(self.current_location())),
                type_args,
            }),
            &start,
        ))
    }

    /// Function to parse a type
    pub fn parse_type(&self) -> AstGenResult<'c, AstNode<'c, Type<'c>>> {
        let token = self
            .peek()
            .ok_or_else(|| self.unexpected_eof::<()>().err().unwrap())?;

        let start = token.span;
        let variant = match &token.kind {
            TokenKind::Amp => {
                self.skip_token();

                // Check if this is a raw ref by checking if the keyword is present...
                let is_ref = match self.peek() {
                    Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Raw)) => {
                        self.skip_token();
                        true
                    }
                    _ => false,
                };

                match self.parse_type() {
                    Ok(ty) if is_ref => Type::RawRef(RawRefType(ty)),
                    Ok(ty) => Type::Ref(RefType(ty)),
                    err => return err,
                }
            }
            // This is a type var
            TokenKind::Dollar => {
                self.skip_token();
                let name = self.parse_ident()?;

                Type::TypeVar(TypeVar { name })
            }
            TokenKind::Question => {
                self.skip_token();
                Type::Existential(ExistentialType)
            }
            TokenKind::Ident(id) => {
                self.skip_token();

                let (name, args) = self.parse_name_with_type_args(id)?;
                // if the type_args are None, this means that the name could be either a
                // infer_type, or a type_var...
                match args {
                    Some(type_args) => Type::Named(NamedType { name, type_args }),
                    None => {
                        // @@Cleanup: This produces an AstNode<AccessName> whereas we just want the single name...
                        let ident = name.body().path.get(0).unwrap();

                        match *ident {
                            i if i == CORE_IDENTIFIERS.underscore => Type::Infer(InferType),
                            _ => Type::Named(NamedType {
                                name,
                                type_args: AstNodes::empty(),
                            }),
                        }
                    }
                }
            }

            // Map or set type
            TokenKind::Tree(Delimiter::Brace, tree_index) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, token.span);

                let lhs_type = gen.parse_type()?;

                match gen.peek() {
                    // This must be a map
                    Some(token) if token.has_kind(TokenKind::Colon) => {
                        gen.skip_token();

                        let rhs_type = gen.parse_type()?;

                        // @@CopyPasta
                        if gen.has_token() {
                            gen.expected_eof()?;
                        }

                        // @@Incomplete: inline type names into ident map...
                        let name = IDENTIFIER_MAP.create_ident(MAP_TYPE_NAME);

                        Type::Named(NamedType {
                            name: self.make_access_name_from_identifier(name, token.span),
                            type_args: ast_nodes![&self.wall; lhs_type, rhs_type],
                        })
                    }
                    Some(_) => gen.expected_eof()?,
                    None => {
                        // @@Incomplete: inline type names into ident map...
                        let name = IDENTIFIER_MAP.create_ident(SET_TYPE_NAME);

                        Type::Named(NamedType {
                            name: self.make_access_name_from_identifier(name, token.span),
                            type_args: ast_nodes![&self.wall; lhs_type],
                        })
                    }
                }
            }

            // List type
            TokenKind::Tree(Delimiter::Bracket, tree_index) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, token.span);

                let inner_type = gen.parse_type()?;

                // @@CopyPasta
                if gen.has_token() {
                    gen.expected_eof()?;
                }

                // @@Incomplete: inline type names into ident map...
                let name = IDENTIFIER_MAP.create_ident(LIST_TYPE_NAME);

                Type::Named(NamedType {
                    name: self.make_access_name_from_identifier(name, token.span),
                    type_args: ast_nodes![&self.wall; inner_type],
                })
            }

            // Tuple or function type
            TokenKind::Tree(Delimiter::Paren, _) => self
                .parse_function_or_tuple_type(false)?
                .into_body()
                .move_out(),
            _ => self.error(AstGenErrorKind::ExpectedType, None, None)?,
        };

        Ok(self.node_from_joined_location(variant, &start))
    }

    /// Parse an single name or a function call that is applied on the left hand side
    /// expression. Infix calls and name are only separated by infix calls having
    /// parenthesees at the end of the name.
    pub fn parse_name_or_infix_call(&self) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Dot));

        let start = self.current_location();

        match &self.next_token() {
            Some(Token {
                kind: TokenKind::Ident(id),
                span: id_span,
            }) => {
                let type_args = self.peek_resultant_fn(|| self.parse_type_args());
                let type_args = type_args.unwrap_or_else(AstNodes::empty);

                // create the subject of the call
                let subject = self.node_with_location(
                    Expression::new(ExpressionKind::Variable(VariableExpr {
                        name: self.make_access_name_from_identifier(*id, *id_span),
                        type_args,
                    })),
                    start.join(self.current_location()),
                );

                match self.peek() {
                    Some(Token {
                        kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                        span,
                    }) => {
                        // Eat the generator now...
                        self.skip_token();

                        // @@Parallelisable: Since this is a vector of tokens, we should be able to give the resolver, create a new
                        //                   generator and form function call arguments from the stream...
                        let mut args = self.node_with_location(
                            FunctionCallArgs {
                                entries: AstNodes::empty(),
                            },
                            *span,
                        );

                        // so we know that this is the beginning of the function call, so we have to essentially parse an arbitrary number
                        // of expressions separated by commas as arguments to the call.
                        let tree = self.token_trees.get(*tree_index).unwrap();
                        let gen = self.from_stream(tree, *span);

                        while gen.has_token() {
                            let arg = gen.parse_expression_with_precedence(0);
                            args.entries.nodes.push(arg?, &self.wall);

                            // now we eat the next token, checking that it is a comma
                            match gen.peek() {
                                Some(token) if token.has_kind(TokenKind::Comma) => gen.next_token(),
                                _ => break,
                            };
                        }

                        Ok(self.node_with_location(
                            Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                                subject,
                                args,
                            })),
                            start.join(self.current_location()),
                        ))
                    }
                    _ => Ok(subject),
                }
            }
            _ => self.error(AstGenErrorKind::InfixCall, None, None)?,
        }
    }

    /// Parse either a block, a set, or a map. The function has to parse
    /// an initial expression and then determine the type of needed parsing
    /// by the following operator, whether it is a colon, comma or a semicolon.
    pub fn parse_block_or_braced_literal(
        &self,
        tree: &'stream Row<'stream, Token>,
        span: &Location,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, *span);

        // handle two special cases for empty map and set literals, if the only token
        // is a colon, this must be a map literal, or if the only token is a comma it is
        // an empty set literal.
        if gen.stream.len() == 1 {
            match gen.peek().unwrap() {
                token if token.has_kind(TokenKind::Colon) => {
                    return Ok(self.node_from_location(
                        Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                            self.node_from_location(
                                Literal::Map(MapLiteral {
                                    elements: AstNodes::empty(),
                                }),
                                span,
                            ),
                        ))),
                        span,
                    ))
                }
                token if token.has_kind(TokenKind::Comma) => {
                    return Ok(self.node_from_location(
                        Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                            self.node_from_location(
                                Literal::Set(SetLiteral {
                                    elements: AstNodes::empty(),
                                }),
                                span,
                            ),
                        ))),
                        span,
                    ))
                }
                _ => (),
            }
        }

        // Is this an empty block?
        if !gen.has_token() {
            return Ok(self.node_from_location(
                Expression::new(ExpressionKind::Block(BlockExpr(self.node_from_location(
                    Block::Body(BodyBlock {
                        statements: AstNodes::empty(),
                        expr: None,
                    }),
                    span,
                )))),
                span,
            ));
        }

        // Here we have to parse the initial expression and then check if there is a specific
        // separator. We have to check:
        //
        // - If an expression is followed by a comma separator, it must be a set literal.
        //
        // - If an expression is followed by a ':' (colon), it must be a map literal.
        //
        // - Otherwise, it must be a block and we should continue parsing the block from here
        let initial_offset = gen.offset();
        let expr = gen.parse_expression();

        match (gen.peek(), expr) {
            (Some(token), Ok(expr)) if token.has_kind(TokenKind::Comma) => {
                gen.skip_token(); // ','

                let literal = self.parse_set_literal(gen, expr)?;

                Ok(self.node_from_location(
                    Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(literal))),
                    span,
                ))
            }
            (Some(token), Ok(expr)) if token.has_kind(TokenKind::Colon) => {
                gen.skip_token(); // ':'

                let start_pos = expr.location();
                let entry = self.node_from_joined_location(
                    MapLiteralEntry {
                        key: expr,
                        value: gen.parse_expression_with_precedence(0)?,
                    },
                    &start_pos,
                );

                // Peek ahead to check if there is a comma, if there is then we'll parse more map entries,
                // and pass it into parse_map_literal.
                match gen.peek() {
                    Some(token) if token.has_kind(TokenKind::Comma) => {
                        gen.skip_token();

                        let literal = self.parse_map_literal(gen, entry)?;

                        Ok(self.node_from_location(
                            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(literal))),
                            span,
                        ))
                    }
                    _ => Ok(self.node_from_location(
                        Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                            self.node_from_location(
                                Literal::Map(MapLiteral {
                                    elements: ast_nodes![&self.wall; entry],
                                }),
                                span,
                            ),
                        ))),
                        span,
                    )),
                }
            }
            (Some(_), _) => {
                // reset the position and attempt to parse a statement
                gen.offset.set(initial_offset);
                let statement = gen.parse_statement()?;

                // check here if there is a 'semi', and then convert the expression into a statement.
                let block = self.parse_block_from_gen(&gen, *span, Some(statement))?;

                Ok(self.node_from_location(
                    Expression::new(ExpressionKind::Block(BlockExpr(block))),
                    span,
                ))
            }
            (None, Ok(expr)) => {
                // This block is just a block with a single expression

                Ok(self.node_from_location(
                    Expression::new(ExpressionKind::Block(BlockExpr(self.node_from_location(
                        Block::Body(BodyBlock {
                            statements: AstNodes::empty(),
                            expr: Some(expr),
                        }),
                        span,
                    )))),
                    span,
                ))
            }
            (None, Err(_)) => {
                // reset the position and attempt to parse a statement
                gen.offset.set(initial_offset);
                let statement = gen.parse_statement()?;

                Ok(self.node_from_location(
                    Expression::new(ExpressionKind::Block(BlockExpr(self.node_from_location(
                        Block::Body(BodyBlock {
                            statements: ast_nodes![&self.wall; statement],
                            expr: None,
                        }),
                        span,
                    )))),
                    span,
                ))
            }
        }
    }

    /// Parse a single map entry in a literal.
    pub fn parse_map_entry(&self) -> AstGenResult<'c, AstNode<'c, MapLiteralEntry<'c>>> {
        let start = self.current_location();

        let key = self.parse_expression_with_precedence(0)?;
        self.parse_token_atom(TokenKind::Colon)?;
        let value = self.parse_expression_with_precedence(0)?;

        Ok(self.node_from_joined_location(MapLiteralEntry { key, value }, &start))
    }

    /// Parse a map literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub fn parse_map_literal(
        &self,
        gen: Self,
        initial_entry: AstNode<'c, MapLiteralEntry<'c>>,
    ) -> AstGenResult<'c, AstNode<'c, Literal<'c>>> {
        let start = gen.current_location();
        let mut elements = gen.parse_separated_fn(
            || gen.parse_map_entry(),
            || gen.parse_token_atom(TokenKind::Comma),
        )?;

        elements.nodes.insert(0, initial_entry, &self.wall);

        Ok(self.node_from_joined_location(Literal::Map(MapLiteral { elements }), &start))
    }

    /// Parse a set literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub fn parse_set_literal(
        &self,
        gen: Self,
        initial_entry: AstNode<'c, Expression<'c>>,
    ) -> AstGenResult<'c, AstNode<'c, Literal<'c>>> {
        let start = self.current_location();

        let mut elements = gen.parse_separated_fn(
            || gen.parse_expression_with_precedence(0),
            || gen.parse_token_atom(TokenKind::Comma),
        )?;

        // insert the first item into elements
        elements.nodes.insert(0, initial_entry, &self.wall);

        Ok(self.node_from_joined_location(Literal::Set(SetLiteral { elements }), &start))
    }

    /// Parse a pattern with an optional if guard after the singular pattern.
    pub fn parse_pattern_with_if(&self) -> AstGenResult<'c, AstNode<'c, Pattern<'c>>> {
        let start = self.next_location();
        let pattern = self.parse_singular_pattern()?;

        match self.peek() {
            Some(token) if token.has_kind(TokenKind::Keyword(Keyword::If)) => {
                self.skip_token();

                let condition = self.parse_expression_with_precedence(0)?;

                Ok(self.node_from_joined_location(
                    Pattern::If(IfPattern { pattern, condition }),
                    &start,
                ))
            }
            _ => Ok(pattern),
        }
    }

    /// Parse a compound pattern.
    pub fn parse_pattern(&self) -> AstGenResult<'c, AstNode<'c, Pattern<'c>>> {
        // attempt to get the next token location as we're starting a pattern here, if there is no token
        // we should exit and return an error
        let start = self.next_location();

        // Parse the first pattern, but throw away the location information since that will be
        // computed at the end anyway...
        let mut patterns = ast_nodes![&self.wall;];

        while self.has_token() {
            let pattern = self.parse_pattern_with_if()?;
            patterns.nodes.push(pattern, &self.wall);

            // Check if this is going to be another pattern following the current one.
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Pipe) => {
                    self.skip_token();
                }
                _ => break,
            }
        }

        // if the length of patterns is greater than one, we return an 'OR' pattern,
        // otherwise just the first pattern.
        if patterns.len() == 1 {
            let pat = patterns.nodes.pop().unwrap();
            Ok(pat)
        } else {
            Ok(self
                .node_from_joined_location(Pattern::Or(OrPattern { variants: patterns }), &start))
        }
    }

    /// Parse a function definition argument, which is made of an identifier and a function type.
    pub fn parse_function_def_arg(&self) -> AstGenResult<'c, AstNode<'c, FunctionDefArg<'c>>> {
        let name = self.parse_ident()?;
        let start = name.location();

        // @@Future: default values for argument...
        let ty = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Colon) => {
                self.skip_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        Ok(self.node_from_joined_location(FunctionDefArg { name, ty }, &start))
    }

    /// Parse a function literal. Function literals are essentially definitions of lambdas
    /// that can be assigned to variables or passed as arguments into other functions.
    pub fn parse_function_literal(
        &self,
        gen: &Self,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let start = self.current_location();

        // parse function definition arguments.
        let args = gen.parse_separated_fn(
            || gen.parse_function_def_arg(),
            || gen.parse_token_atom(TokenKind::Comma),
        )?;

        // check if there is a return type
        let return_ty = match self.peek_resultant_fn(|| self.parse_token_atom(TokenKind::Colon)) {
            Some(_) => Some(self.parse_type()?),
            _ => None,
        };

        self.parse_arrow()?;

        let fn_body = match self.peek() {
            Some(_) => self.parse_expression_with_precedence(0)?,
            None => self.error(AstGenErrorKind::ExpectedFnBody, None, None)?,
        };

        Ok(self.node_from_joined_location(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                gen.node_from_joined_location(
                    Literal::Function(FunctionDef {
                        args,
                        return_ty,
                        fn_body,
                    }),
                    &start,
                ),
            ))),
            &start,
        ))
    }

    /// Function to either parse an expression that is wrapped in parentheses or a tuple literal. If this
    /// is a tuple literal, the first expression must be followed by a comma separator, after that the comma
    /// after the expression is optional.
    ///
    ///
    /// Tuples have a familiar syntax with many other languages, but exhibit two distinct differences between the common syntax.
    /// These differences are:
    ///
    /// - Empty tuples: (,)
    /// - Singleton tuple : (A,)
    /// - Many membered tuple: (A, B, C) or (A, B, C,)
    ///
    pub fn parse_expression_or_tuple(
        &self,
        tree: &'stream Row<'stream, Token>,
        span: &Location,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, *span);
        let start = self.current_location();

        // Handle the empty tuple case
        if gen.stream.len() == 1 {
            match gen.peek().unwrap() {
                token if token.has_kind(TokenKind::Comma) => {
                    gen.skip_token();

                    return Ok(gen.node_from_joined_location(
                        Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                            gen.node_from_joined_location(
                                Literal::Tuple(TupleLiteral {
                                    elements: ast_nodes![&self.wall;],
                                }),
                                &start,
                            ),
                        ))),
                        &start,
                    ));
                }
                _ => (),
            };
        }

        let lhs = gen.parse_expression_with_precedence(0)?;
        let (expr, re_assigned) = gen.try_parse_re_assignment_operation(lhs)?;

        if re_assigned && gen.peek().is_some() {
            return gen.error(AstGenErrorKind::EOF, None, Some(gen.peek().unwrap().kind));
        }

        // Check if this is just a singularly wrapped expression
        if gen.peek().is_none() {
            return Ok(expr);
        }

        let mut elements = ast_nodes![&self.wall; expr];

        loop {
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    gen.skip_token();

                    // Handles the case where this is a trailing comma and no tokens after...
                    if !gen.has_token() {
                        break;
                    }

                    elements
                        .nodes
                        .push(gen.parse_expression_with_precedence(0)?, &self.wall)
                }
                Some(token) => gen.error(
                    AstGenErrorKind::ExpectedExpression,
                    Some(TokenKindVector::begin_expression(&self.wall)),
                    Some(token.kind),
                )?,
                None => break,
            }
        }

        Ok(gen.node_from_joined_location(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                gen.node_from_joined_location(Literal::Tuple(TupleLiteral { elements }), &start),
            ))),
            &start,
        ))
    }

    /// Parse an array literal.
    pub fn parse_array_literal(
        &self,
        tree: &'stream Row<'stream, Token>,
        span: &Location,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, *span);
        let start = gen.current_location();

        let mut elements = AstNodes::empty();

        while gen.has_token() {
            let expr = gen.parse_expression_with_precedence(0)?;
            elements.nodes.push(expr, &self.wall);

            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    gen.skip_token();
                }
                Some(token) => {
                    // if we haven't exhausted the whole token stream, then report this as a unexpected
                    // token error
                    return gen.error(
                        AstGenErrorKind::Expected,
                        Some(TokenKindVector::singleton(&self.wall, TokenKind::Comma)),
                        Some(token.kind),
                    );
                }
                None => break,
            }
        }

        Ok(gen.node_from_joined_location(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                gen.node_from_joined_location(Literal::List(ListLiteral { elements }), &start),
            ))),
            &start,
        ))
    }

    /// Convert a literal kind into a pattern literal kind.
    pub fn convert_literal_kind_into_pattern(&self, kind: &TokenKind) -> LiteralPattern {
        match kind {
            TokenKind::StrLiteral(s) => LiteralPattern::Str(StrLiteralPattern(*s)),
            TokenKind::CharLiteral(s) => LiteralPattern::Char(CharLiteralPattern(*s)),
            TokenKind::IntLiteral(s) => LiteralPattern::Int(IntLiteralPattern(*s)),
            TokenKind::FloatLiteral(s) => LiteralPattern::Float(FloatLiteralPattern(*s)),
            _ => unreachable!(),
        }
    }

    /// Convert the current token (provided it is a primitive literal) into a [ExpressionKind::LiteralExpr]
    /// by simply matching on the type of the expr.
    pub fn parse_literal(&self) -> AstNode<'c, Expression<'c>> {
        let token = self.current_token();
        let literal = AstNode::new(
            match token.kind {
                TokenKind::IntLiteral(num) => Literal::Int(IntLiteral(num)),
                TokenKind::FloatLiteral(num) => Literal::Float(FloatLiteral(num)),
                TokenKind::CharLiteral(ch) => Literal::Char(CharLiteral(ch)),
                TokenKind::StrLiteral(str) => Literal::Str(StrLiteral(str)),
                _ => unreachable!(),
            },
            token.span,
            &self.wall,
        );

        self.node_from_location(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(literal))),
            &token.span,
        )
    }

    /// This function is used to pickup 'glued' operator tokens to form more complex binary operators
    /// that might be made up of multiple tokens. The function will peek ahead (2 tokens at most since
    /// all binary operators are made of that many tokens). The function returns an optional derived
    /// operator, and the number of tokens that was consumed deriving the operator, it is the responsibility
    /// of the caller to increment the token stream by the provided number.
    pub(crate) fn parse_operator(&self) -> (Option<Operator>, u8) {
        let token = self.peek();

        // check if there is a token that we can peek at ahead...
        if token.is_none() {
            return (None, 0);
        }

        let (op, mut consumed): (_, u8) = match &(token.unwrap()).kind {
            // Since the 'as' keyword is also a binary operator, we have to handle it here...
            TokenKind::Keyword(Keyword::As) => (Some(OperatorKind::As), 1),
            TokenKind::Eq => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::EqEq), 2),
                _ => (None, 0),
            },
            TokenKind::Lt => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::LtEq), 2),
                Some(token) if token.kind == TokenKind::Lt => (Some(OperatorKind::Shl), 2),
                _ => (Some(OperatorKind::Lt), 1),
            },
            TokenKind::Gt => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::GtEq), 2),
                Some(token) if token.kind == TokenKind::Gt => (Some(OperatorKind::Shr), 2),
                _ => (Some(OperatorKind::Gt), 1),
            },
            TokenKind::Plus => (Some(OperatorKind::Add), 1),
            TokenKind::Minus => (Some(OperatorKind::Sub), 1),
            TokenKind::Star => (Some(OperatorKind::Mul), 1),
            TokenKind::Slash => (Some(OperatorKind::Div), 1),
            TokenKind::Percent => (Some(OperatorKind::Mod), 1),
            TokenKind::Caret => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Caret => (Some(OperatorKind::Exp), 2),
                _ => (Some(OperatorKind::BitXor), 1),
            },
            TokenKind::Amp => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Amp => (Some(OperatorKind::And), 2),
                _ => (Some(OperatorKind::BitAnd), 1),
            },
            TokenKind::Pipe => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Pipe => (Some(OperatorKind::Or), 2),
                _ => (Some(OperatorKind::BitOr), 1),
            },
            TokenKind::Exclamation => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(OperatorKind::NotEq), 2),
                _ => (None, 0), // this is a unary operator '!'
            },
            _ => (None, 0),
        };

        match op {
            // check if the operator is re-assignable and if so try to parse a equality operator.
            // If we see this one then we can parse and then just convert the operator into the
            // 'Eq' version.
            Some(kind) => {
                let assignable = match self.peek_nth(consumed as usize) {
                    Some(token) if kind.is_re_assignable() && token.has_kind(TokenKind::Eq) => {
                        consumed += 1;
                        true
                    }
                    _ => false,
                };

                (Some(Operator { kind, assignable }), consumed)
            }
            None => (None, 0),
        }
    }
}
