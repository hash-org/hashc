//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::cell::Cell;

use hash_alloc::Wall;
use hash_alloc::{collections::row::Row, row};

use hash_ast::{
    ast::*,
    error::{ParseError, ParseResult},
    ident::{Identifier, IDENTIFIER_MAP},
    keyword::Keyword,
    literal::STRING_LITERAL_MAP,
    location::{Location, SourceLocation},
    module::ModuleIdx,
    operator::{CompoundFn, OperatorFn},
    resolve::ModuleResolver,
};

use crate::{operator::Operator, token::TokenAtom};
use crate::{
    operator::OperatorKind,
    token::{Delimiter, Token, TokenKind, TokenKindVector},
};

pub struct AstGen<'c, 'stream, 'resolver, R> {
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
    stream: &'stream [Token<'c>],

    /// State set by expression parsers for parents to let them know if the parsed expression
    /// was made up of multiple expressions with precedence operators.
    is_compound_expr: Cell<bool>,

    /// State to prevent from struct literals being parsed in the current expression, because
    /// the parent has specifically checked ahead to ensure it isn't a struct literal.
    disallow_struct_literals: Cell<bool>,

    /// Instance of a [ModuleResolver] to notify the parser of encountered imports.
    resolver: &'resolver R,

    wall: Wall<'c>,
}

/// Implementation of the [AstGen] with accompanying functions to parse specific
/// language components.
impl<'c, 'stream, 'resolver, R> AstGen<'c, 'stream, 'resolver, R>
where
    R: ModuleResolver,
{
    /// Create new AST generator from a token stream.
    pub fn new(stream: &'stream [Token<'c>], resolver: &'resolver R, wall: Wall<'c>) -> Self {
        Self {
            stream,
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
    pub fn from_stream(&self, stream: &'stream [Token<'c>], parent_span: Location) -> Self {
        Self {
            stream,
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
        match self.resolver.module_index() {
            Some(module_index) => SourceLocation {
                location: *location,
                module_index,
            },
            None => SourceLocation {
                location: *location,
                module_index: ModuleIdx(0),
            },
        }
    }

    /// Get the current offset of where the stream is at.
    #[inline(always)]
    pub(crate) fn offset(&self) -> usize {
        self.offset.get()
    }

    /// Function to peek at the nth token ahead of the current offset.
    pub(crate) fn peek_nth(&self, at: usize) -> Option<&Token<'c>> {
        self.stream.get(self.offset.get() + at)
    }

    /// Attempt to peek one step token ahead.
    pub(crate) fn peek(&self) -> Option<&Token<'c>> {
        self.peek_nth(0)
    }

    /// Peek two tokens ahead.
    pub(crate) fn peek_second(&self) -> Option<&Token<'c>> {
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
    pub(crate) fn next_token(&self) -> Option<&Token<'c>> {
        let value = self.stream.get(self.offset.get());

        if value.is_some() {
            // @@UnsafeLibUsage
            self.offset.update::<_>(|x| x + 1);
        }

        value
    }

    /// Get the current token in the stream.
    pub(crate) fn current_token(&self) -> &Token<'c> {
        self.stream.get(self.offset.get() - 1).unwrap()
    }

    /// Get the current location from the current token, if there is no token at the current
    /// offset, then the location of the last token is used.
    #[inline(always)]
    pub(crate) fn current_location(&self) -> Location {
        // check that the length of current generator is at least one...
        if self.stream.is_empty() {
            return self.parent_span.unwrap_or_default();
        }

        match self.stream.get(self.offset()) {
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
                let Token {span, kind: _} = self.current_token();
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

    /// Function to create a token error at the current location with a
    /// vector of tokens that the parser was accepting in the current state.
    pub(crate) fn unexpected_token_error<T>(
        &self,
        kind: &TokenKind,
        expected: &TokenKindVector,
        location: &Location,
    ) -> ParseResult<T> {
        // we need to convert a token-tree into just the delimiter since we don't want
        // to print the whole tree...
        let atom = kind.to_atom();

        if expected.is_empty() {
            self.error_with_location(format!("Unexpected token '{}'", atom), location)
        } else {
            self.error_with_location(
                format!("Unexpected token '{}', expecting {}", atom, expected),
                location,
            )
        }
    }

    /// Create an error at the current location.
    pub fn error<T, S: Into<String>>(&self, message: S) -> ParseResult<T> {
        Err(ParseError::Parsing {
            message: message.into(),
            src: self.source_location(&self.current_location()),
        })
    }

    /// Create an error at the current location.
    pub fn error_with_location<T, S: Into<String>>(
        &self,
        message: S,
        location: &Location,
    ) -> ParseResult<T> {
        Err(ParseError::Parsing {
            message: message.into(),
            src: self.source_location(location),
        })
    }

    pub(crate) fn expected_eof<T>(&self) -> ParseResult<T> {
        // move onto the next token
        self.offset.set(self.offset.get() + 1);

        self.error(format!(
            "Expected the end of a definition, but got '{}'.",
            self.current_token().kind
        ))
    }

    /// Create a generalised "Reached end of file..." error.
    pub(crate) fn unexpected_eof<T>(&self) -> ParseResult<T> {
        self.error("Unexpectedly reached the end of file.")
    }

    /// Create a generalised "Reached end of file..." error.
    pub(crate) fn unexpected_eof_with_ctx<T>(&self, ctx: impl Into<String>) -> ParseResult<T> {
        self.error(format!(
            "{}: but unexpectedly reached the end of file.",
            ctx.into()
        ))
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
                type_args: row![&self.wall],
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
            args: row![&self.wall],
        }))
    }

    /// Utility function for creating a variable from a given name.
    fn make_variable(&self, name: AstNode<'c, AccessName<'c>>) -> AstNode<'c, Expression<'c>> {
        self.node(Expression::new(ExpressionKind::Variable(VariableExpr {
            name,
            type_args: row![&self.wall],
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
                type_args: row![&self.wall],
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
    /// in a [ParseResult]. If The result is an error, or the option is [None], the function will
    /// reset the current offset of the token stream to where it was the function was peeked.
    pub fn peek_fn<T>(
        &self,
        parse_fn: impl Fn() -> ParseResult<Option<T>>,
    ) -> ParseResult<Option<T>> {
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
    /// to where it was the function was peeked. This is essentially a convertor from a [ParseResult<T>]
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
    pub fn parse_module(&self) -> ParseResult<Module<'c>> {
        let mut contents = row![&self.wall];

        while self.has_token() {
            contents.push(self.parse_statement()?, &self.wall);
        }

        Ok(Module { contents })
    }

    /// Parse a statement.
    pub fn parse_statement(&self) -> ParseResult<AstNode<'c, Statement<'c>>> {
        let start = self.current_location();

        match self.peek() {
            Some(Token { kind, span: _ }) if kind.begins_statement() => {
                self.skip_token();

                let atom = kind.to_atom();

                let statement = match atom {
                    TokenAtom::Keyword(Keyword::Let) => Statement::Let(self.parse_let_statement()?),
                    TokenAtom::Keyword(Keyword::Trait) => {
                        Statement::TraitDef(self.parse_trait_defn()?)
                    }
                    TokenAtom::Keyword(Keyword::Enum) => {
                        Statement::EnumDef(self.parse_enum_defn()?)
                    }
                    TokenAtom::Keyword(Keyword::Struct) => {
                        Statement::StructDef(self.parse_struct_defn()?)
                    }
                    TokenAtom::Keyword(Keyword::Continue) => Statement::Continue,
                    TokenAtom::Keyword(Keyword::Break) => Statement::Break,
                    TokenAtom::Keyword(Keyword::Return) => {
                        // @@Hack: check if the next token is a semi-colon, if so the return statement
                        // has no returned expression...
                        match self.peek() {
                            Some(token) if token.has_atom(TokenAtom::Semi) => {
                                Statement::Return(None)
                            }
                            Some(_) => {
                                Statement::Return(Some(self.parse_expression_with_precedence(0)?))
                            }
                            None => Statement::Return(None),
                        }
                    }
                    _ => unreachable!(),
                };

                match self.next_token() {
                    Some(token) if token.has_atom(TokenAtom::Semi) => {
                        Ok(self.node_from_joined_location(statement, &start))
                    }
                    Some(token) => self.error(format!(
                        "Expecting ';' at the end of a statement, but got '{}' ",
                        token.kind
                    )),
                    None => self.unexpected_eof_with_ctx(format!(
                        "'{}', Expecting ';' ending a statement",
                        atom
                    ))?,
                }
            }
            Some(_) => {
                let expr = self.parse_expression_with_precedence(0)?;

                if let Some(op) = self.peek_resultant_fn(|| self.parse_re_assignment_op()) {
                    let transformed_op: OperatorFn = op.into();

                    // Parse the rhs and the semi
                    let rhs = self.parse_expression_with_precedence(0)?;
                    self.parse_token_atom(TokenAtom::Semi)?;

                    // Now we need to transform the re-assignment operator into a function call

                    return Ok(self.node_from_joined_location(
                        Statement::Expr(self.transform_binary_expression(
                            expr,
                            rhs,
                            transformed_op,
                        )),
                        &start,
                    ));
                }

                // Ensure that the next token is a Semi
                match self.peek() {
                    Some(token) if token.has_atom(TokenAtom::Semi) => {
                        self.skip_token();
                        Ok(self.node_from_location(Statement::Expr(expr), &start))
                    }
                    Some(token) if token.has_atom(TokenAtom::Eq) => {
                        self.skip_token();

                        // Parse the rhs and the semi
                        let rhs = self.parse_expression_with_precedence(0)?;
                        self.parse_token_atom(TokenAtom::Semi)?;

                        Ok(self.node_from_joined_location(
                            Statement::Assign(AssignStatement { lhs: expr, rhs }),
                            &start,
                        ))
                    }

                    // Special case where there is a expression at the end of the stream and therefore it
                    // is signifying that it is returning the expression value here
                    None => Ok(self.node_from_location(Statement::Expr(expr), &start)),

                    token => match (token, expr.into_body().move_out().into_kind()) {
                        (_, ExpressionKind::Block(block)) => {
                            Ok(self.node_from_location(Statement::Block(block), &start))
                        }
                        (Some(token), _) => self.error(format!(
                            "Expecting ';' at the end of a statement, but got '{}' ",
                            token.kind
                        ))?,
                        (None, _) => unreachable!(),
                    },
                }
            }
            _ => self.error("Expected statement.")?,
        }
    }

    /// This function is used to exclusively parse a interactive block which follows
    /// similar rules to a an actual block. Interactive statements are like ghost blocks
    /// without the actual braces to begin with. It follows that there are an arbitrary
    /// number of statements, followed by an optional final expression which doesn't
    /// need to be completed by a comma...
    pub fn parse_expression_from_interactive(&self) -> ParseResult<AstNode<'c, BodyBlock<'c>>> {
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
            true => self.node(Expression::new(ExpressionKind::Ref(expr, RefKind::Normal))),
            false => expr,
        }
    }

    /// Create an [Expression] from two provided expressions and an [OperatorFn].
    fn transform_binary_expression(
        &self,
        lhs: AstNode<'c, Expression<'c>>,
        rhs: AstNode<'c, Expression<'c>>,
        op: OperatorFn,
    ) -> AstNode<'c, Expression<'c>> {
        match op {
            OperatorFn::Named { name, assigning } => {
                let rhs_location = rhs.location();

                self.node(Expression::new(ExpressionKind::FunctionCall(
                    FunctionCallExpr {
                        subject: self.node(Expression::new(ExpressionKind::Variable(
                            VariableExpr {
                                name: self.make_access_name_from_str(name, self.current_location()),
                                type_args: row![&self.wall],
                            },
                        ))),
                        args: self.node_from_joined_location(
                            FunctionCallArgs {
                                entries: row![&self.wall;
                                    self.transform_expr_into_ref(lhs, assigning),
                                    rhs,
                                ],
                            },
                            &rhs_location,
                        ),
                    },
                )))
            }
            OperatorFn::LazyNamed { name, assigning } => {
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

                self.node(Expression::new(ExpressionKind::FunctionCall(
                    FunctionCallExpr {
                        subject: self.node(Expression::new(ExpressionKind::Variable(
                            VariableExpr {
                                name: self.make_access_name_from_str(name, self.current_location()),
                                type_args: row![&self.wall],
                            },
                        ))),
                        args: self.node(FunctionCallArgs {
                            entries: row![&self.wall;
                                self.transform_expr_into_ref(lhs, assigning),
                                self.node(Expression::new(ExpressionKind::LiteralExpr(self.node(
                                    Literal::Function(FunctionDef {
                                        args: row![&self.wall],
                                        return_ty: None,
                                        fn_body: rhs,
                                    }),
                                ))))
                            ],
                        }),
                    },
                )))
            }
            OperatorFn::Compound { name, assigning } => {
                // for compound functions that include ordering, we essentially transpile
                // into a match block that checks the result of the 'ord' fn call to the
                // 'Ord' enum variants. This also happens for operators such as '>=' which
                // essentially means that we have to check if the result of 'ord()' is either
                // 'Eq' or 'Gt'.
                self.transform_compound_ord_fn(name, assigning, lhs, rhs)
            }
        }
    }

    fn transform_compound_ord_fn(
        &self,
        fn_ty: CompoundFn,
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
                    entries: row![&self.wall; lhs, rhs],
                }),
            },
        )));

        // each tuple bool variant represents a branch the match statement
        // should return 'true' on, and all the rest will return false...
        // the order is (Lt, Eq, Gt)
        let mut branches = match fn_ty {
            CompoundFn::Leq => {
                row![&self.wall; self.node(MatchCase {
                    pattern: self.node(Pattern::Or(OrPattern {
                        variants: row![&self.wall;
                        self.make_enum_pattern_from_str("Lt", location),
                        self.make_enum_pattern_from_str("Eq", location),
                        ],
                    })),
                    expr: self.make_variable(self.make_boolean(true)),
                })]
            }
            CompoundFn::Geq => {
                row![&self.wall; self.node(MatchCase {
                    pattern: self.node(Pattern::Or(OrPattern {
                        variants: row![&self.wall;
                        self.make_enum_pattern_from_str("Gt", location),
                        self.make_enum_pattern_from_str("Eq", location),
                        ],
                    })),
                    expr: self.make_variable(self.make_boolean(true)),
                })]
            }
            CompoundFn::Lt => {
                row![&self.wall; self.node(MatchCase {
                    pattern: self.make_enum_pattern_from_str("Lt", location),
                    expr: self.make_variable(self.make_boolean(false)),
                })]
            }
            CompoundFn::Gt => {
                row![&self.wall; self.node(MatchCase {
                    pattern: self.make_enum_pattern_from_str("Gt", location),
                    expr: self.make_variable(self.make_boolean(false)),
                })]
            }
        };

        // add the '_' case to the branches to return false on any other
        // condition
        branches.push(
            self.node(MatchCase {
                pattern: self.node(Pattern::Ignore),
                expr: self.make_variable(self.make_boolean(false)),
            }),
            &self.wall,
        );

        self.node(Expression::new(ExpressionKind::Block(self.node(
            Block::Match(MatchBlock {
                subject: fn_call,
                cases: branches,
            }),
        ))))
    }

    /// Function to parse an arbitrary number of 'parsing functions' separated by a singular
    /// 'separator' closure. The function has a behaviour of allowing trailing separator. This
    /// will also parse the function until the end of the current generator, and therefore it
    /// is intended to be used with a nested generator.
    pub fn parse_separated_fn<T>(
        &self,
        parse_fn: impl Fn() -> ParseResult<AstNode<'c, T>>,
        separator_fn: impl Fn() -> ParseResult<()>,
    ) -> ParseResult<AstNodes<'c, T>> {
        let mut args = row![&self.wall;];

        // so parse the arguments to the function here... with potential type annotations
        while self.has_token() {
            match self.peek_resultant_fn(&parse_fn) {
                Some(el) => args.push(el, &self.wall),
                None => break,
            }

            if self.has_token() {
                separator_fn()?;
            }
        }
        if self.has_token() {
            self.expected_eof()?;
        }

        Ok(args)
    }

    /// This will parse an operator and check that it is re-assignable, if the operator is not
    /// re-assignable then the result of the function is an [ParseError] since it expects there
    /// to be this operator.
    pub fn parse_re_assignment_op(&self) -> ParseResult<Operator> {
        let (operator, consumed_tokens) = Operator::from_token_stream(self);

        match operator {
            Some(Operator {
                kind,
                assignable: true,
            }) => {
                // consume the number of tokens eaten whilst getting the operator...
                self.offset.update(|x| x + consumed_tokens as usize);

                Ok(Operator {
                    kind,
                    assignable: true,
                })
            }
            _ => self.error("Expected re-assignment operator here."),
        }
    }

    /// Parse a trait definition. AST representation of a trait statement.
    /// A trait statement is essentially a function with no body, with a
    /// for-all node and some genetic type arguments. For example,
    ///
    /// trait eq<T> => (T, T) => bool;
    ///     ┌─^^ ^─┐   ^─ ─ ─ ─ ─ ─ ─ ┐
    ///   name   Generic type args    Function type definition
    pub fn parse_trait_defn(&self) -> ParseResult<TraitDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_atom(TokenAtom::Keyword(Keyword::Trait)));

        let name = self.parse_ident()?;

        self.parse_token_atom(TokenAtom::Eq)?;
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
    pub fn parse_struct_defn(&self) -> ParseResult<StructDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_atom(TokenAtom::Keyword(Keyword::Struct)));

        let name = self.parse_ident()?;
        self.parse_token_atom(TokenAtom::Eq)?;

        let (bound, entries) = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Lt) => {
                let bound = Some(self.parse_type_bound()?);
                self.parse_arrow()?;
                let entries = self.parse_struct_def_entries()?;

                (bound, entries)
            }

            Some(token) if token.is_brace_tree() => {
                let entries = self.parse_struct_def_entries()?;

                (None, entries)
            }
            _ => self.error("Expected struct type args or struct definition entries here")?,
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
    pub fn parse_enum_defn(&self) -> ParseResult<EnumDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_atom(TokenAtom::Keyword(Keyword::Enum)));

        let name = self.parse_ident()?;

        self.parse_token_atom(TokenAtom::Eq)?;

        // now parse the optional type bound and the enum definition entries,
        // if a type bound is specified, then the definition of the struct should
        // be followed by an arrow ('=>')...
        let (bound, entries) = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Lt) => {
                let bound = Some(self.parse_type_bound()?);
                self.parse_arrow()?;

                let entries = self.parse_enum_def_entries()?;

                (bound, entries)
            }

            Some(token) if token.is_brace_tree() => {
                let entries = self.parse_enum_def_entries()?;

                (None, entries)
            }
            _ => self.error("Expected struct type args or struct definition entries here")?,
        };

        Ok(EnumDef {
            name,
            bound,
            entries,
        })
    }

    pub fn parse_enum_def_entries(&self) -> ParseResult<AstNodes<'c, EnumDefEntry<'c>>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree),
                span,
            }) => {
                self.skip_token();

                let gen = self.from_stream(tree, *span);
                gen.parse_separated_fn(
                    || gen.parse_enum_def_entry(),
                    || gen.parse_token_atom(TokenAtom::Comma),
                )
            }
            Some(token) => self.unexpected_token_error(
                &token.kind,
                &TokenKindVector::from_row(
                    row![&self.wall; TokenAtom::Delimiter(Delimiter::Brace, false)],
                ),
                &self.current_location(),
            )?,
            None => self.unexpected_eof(),
        }
    }

    /// Parse an Enum definition entry.
    pub fn parse_enum_def_entry(&self) -> ParseResult<AstNode<'c, EnumDefEntry<'c>>> {
        let start = self.current_location();
        let name = self.parse_ident()?;

        let mut args = row![&self.wall;];

        if let Some(Token {
            kind: TokenKind::Tree(Delimiter::Paren, tree),
            span,
        }) = self.peek()
        {
            self.skip_token();
            let gen = self.from_stream(tree, *span);
            while gen.has_token() {
                let ty = gen.parse_type()?;
                args.push(ty, &self.wall);

                if gen.has_token() {
                    gen.parse_token_atom(TokenAtom::Comma)?;
                }
            }
        }

        Ok(self.node_from_joined_location(EnumDefEntry { name, args }, &start))
    }

    /// Parse struct definition field entries.
    pub fn parse_struct_def_entries(&self) -> ParseResult<AstNodes<'c, StructDefEntry<'c>>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree),
                span,
            }) => {
                self.skip_token();

                let gen = self.from_stream(tree, *span);

                gen.parse_separated_fn(
                    || gen.parse_struct_def_entry(),
                    || gen.parse_token_atom(TokenAtom::Comma),
                )
            }
            Some(token) => self.unexpected_token_error(
                &token.kind,
                &TokenKindVector::from_row(
                    row![&self.wall; TokenAtom::Delimiter(Delimiter::Brace, true)],
                ),
                &self.current_location(),
            )?,
            None => self.unexpected_eof(),
        }
    }

    /// Parse struct definition field.
    pub fn parse_struct_def_entry(&self) -> ParseResult<AstNode<'c, StructDefEntry<'c>>> {
        let start = self.current_location();
        let name = self.parse_ident()?;

        let ty = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Colon) => {
                self.skip_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        let default = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Eq) => {
                self.skip_token();

                Some(self.parse_expression_with_precedence(0)?)
            }
            _ => None,
        };

        Ok(self.node_from_joined_location(StructDefEntry { name, ty, default }, &start))
    }

    /// Parse a type bound. Type bounds can occur in traits, function, struct and enum
    /// definitions.
    pub fn parse_type_bound(&self) -> ParseResult<AstNode<'c, Bound<'c>>> {
        let start = self.current_location();
        let type_args = self.parse_type_args()?;

        let trait_bounds = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Keyword(Keyword::Where)) => {
                self.skip_token();

                let mut trait_bounds = row![&self.wall;];

                loop {
                    match self.peek() {
                        Some(Token {
                            kind: TokenKind::Atom(TokenAtom::Ident(ident)),
                            span: _,
                        }) => {
                            self.skip_token();

                            let bound_start = self.current_location();
                            let (name, type_args) = self.parse_trait_bound(ident)?;

                            trait_bounds.push(
                                self.node_from_joined_location(
                                    TraitBound { name, type_args },
                                    &bound_start,
                                ),
                                &self.wall,
                            );

                            // ensure that the bound is followed by a comma, if not then break...
                            match self.peek() {
                                Some(token) if token.has_atom(TokenAtom::Comma) => {
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
            _ => row![&self.wall;],
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
    pub fn parse_for_loop(&self) -> ParseResult<AstNode<'c, Block<'c>>> {
        debug_assert!(self
            .current_token()
            .has_atom(TokenAtom::Keyword(Keyword::For)));

        let start = self.current_location();

        // now we parse the singular pattern that begins at the for-loop
        let pattern = self.parse_pattern()?;
        let pattern_location = pattern.location();

        self.parse_token_atom(TokenAtom::Keyword(Keyword::In))?;

        self.disallow_struct_literals.set(true);
        let iterator = self.parse_expression_with_precedence(0)?;
        let iterator_location = iterator.location();
        self.disallow_struct_literals.set(false);

        let body = self.parse_block()?;
        let body_location = body.location();

        // transpile the for loop
        Ok(self.node_from_joined_location(Block::Loop(self.node_from_location(
            Block::Match(MatchBlock {
            subject: self.node(Expression::new(ExpressionKind::FunctionCall(
                FunctionCallExpr {
                    subject: self.node(Expression::new(ExpressionKind::Variable(
                        VariableExpr {
                            name: self.make_access_name_from_str("next", iterator.location()),
                            type_args: row![&self.wall],
                        },
                    ))),
                    args: self.node_from_location(FunctionCallArgs {
                        entries: row![&self.wall; iterator],
                    }, &iterator_location),
                },
            ))),
            cases: row![&self.wall; self.node_from_location(MatchCase {
                    pattern: self.node_from_location(
                        Pattern::Enum(
                            EnumPattern {
                                name:
                                    self.make_access_name_from_str(
                                        "Some",
                                        self.current_location()
                                    ),
                                args: row![&self.wall; pattern],
                            },
                        ), &pattern_location
                    ),
                    expr: self.node_from_location(Expression::new(ExpressionKind::Block(body)), &body_location),
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
                                args: row![&self.wall],
                            },
                        ),
                    ),
                    expr: self.node(Expression::new(ExpressionKind::Block(
                        self.node(Block::Body(BodyBlock {
                            statements: row![&self.wall; self.node(Statement::Break)],
                            expr: None,
                        })),
                    ))),
                }),
            ],
        }), &start)), &start))
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
    pub fn parse_while_loop(&self) -> ParseResult<AstNode<'c, Block<'c>>> {
        debug_assert!(self
            .current_token()
            .has_atom(TokenAtom::Keyword(Keyword::While)));

        let start = self.current_location();

        self.disallow_struct_literals.set(true);
        let condition = self.parse_expression_with_precedence(0)?;
        let condition_location = condition.location();
        self.disallow_struct_literals.set(false);

        let body = self.parse_block()?;
        let body_location = body.location();

        Ok(self.node_from_joined_location(
            Block::Loop(self.node_with_location(
                Block::Match(MatchBlock {
                    subject: condition,
                    cases: row![&self.wall; self.node(MatchCase {
                            pattern: self.node(Pattern::Enum(EnumPattern {
                                name: self.make_access_name_from_str("true", body_location),
                                args: row![&self.wall],
                            })),
                            expr: self.node(Expression::new(ExpressionKind::Block(body))),
                        }),
                        self.node(MatchCase {
                            pattern: self.node(Pattern::Enum(EnumPattern {
                                name: self.make_access_name_from_str("false", body_location),
                                args: row![&self.wall],
                            })),
                            expr: self.node(Expression::new(ExpressionKind::Block(
                                self.node(Block::Body(BodyBlock {
                                    statements: row![&self.wall; self.node(Statement::Break)],
                                    expr: None,
                                })),
                            ))),
                        }),
                    ],
                }),
                condition_location,
            )),
            &start,
        ))
    }

    /// Parse a match case. A match case involves handling the pattern and the
    /// expression branch.
    pub fn parse_match_case(&self) -> ParseResult<AstNode<'c, MatchCase<'c>>> {
        let start = self.current_location();
        let pattern = self.parse_pattern()?;

        self.parse_arrow()?;
        let expr = self.parse_expression_with_precedence(0)?;

        Ok(self.node_from_joined_location(MatchCase { pattern, expr }, &start))
    }

    /// Parse a match block statement, which is composed of a subject and an arbitrary
    /// number of match cases that are surrounded in braces.
    pub fn parse_match_block(&self) -> ParseResult<AstNode<'c, Block<'c>>> {
        debug_assert!(self
            .current_token()
            .has_atom(TokenAtom::Keyword(Keyword::Match)));

        let start = self.current_location();

        self.disallow_struct_literals.set(true);
        let subject = self.parse_expression_with_precedence(0)?;
        self.disallow_struct_literals.set(false);

        let mut cases = row![&self.wall];
        // cases are wrapped in a brace tree
        match self.peek() {
            Some(token) if token.is_brace_tree() => {
                let (tree, span) = self.next_token().unwrap().into_tree();
                let gen = self.from_stream(tree, span);

                while gen.has_token() {
                    cases.push(gen.parse_match_case()?, &self.wall);

                    gen.parse_token_atom(TokenAtom::Semi)?;
                }
            }
            Some(token) => self.unexpected_token_error(
                &token.kind,
                &TokenKindVector::from_row(
                    row![&self.wall; TokenAtom::Delimiter(Delimiter::Brace, true)],
                ),
                &self.current_location(),
            )?,
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
    pub fn parse_if_statement(&self) -> ParseResult<AstNode<'c, Block<'c>>> {
        debug_assert!(matches!(
            self.current_token().kind,
            TokenKind::Atom(TokenAtom::Keyword(Keyword::If))
        ));

        let start = self.current_location();

        let mut cases = row![&self.wall];
        let mut has_else_branch = false;

        while self.has_token() {
            // @@Cleanup: @@Hack: essentially because struct literals begin with an ident and then a block
            //    this creates an ambiguity for the parser because it could also just be an ident
            //    and then a block, therefore, we have to peek ahead to see if we can see two following
            //    trees ('{...}') and if so, then we don't disallow parsing a struct literal, if it's
            //    only one token tree, we prevent it from being parsed as a struct literal
            //    by updating the global state...
            // self.disallow_struct_literals
            //     .set(self.lookahead_for_struct_literal());
            self.disallow_struct_literals.set(true);

            let clause = self.parse_expression_with_precedence(0)?;
            let clause_loc = clause.location();

            // We can re-enable struct literals
            self.disallow_struct_literals.set(false);

            let branch = self.parse_block()?;
            let branch_loc = branch.location();

            cases.push(
                self.node_from_location(
                    MatchCase {
                        pattern: self.node_from_location(
                            Pattern::If(IfPattern {
                                pattern: self.node_from_location(Pattern::Ignore, &clause_loc),
                                condition: clause,
                            }),
                            &clause_loc,
                        ),
                        expr: self.node_from_location(
                            Expression::new(ExpressionKind::Block(branch)),
                            &branch_loc,
                        ),
                    },
                    &clause_loc.join(branch_loc),
                ),
                &self.wall,
            );

            // Now check if there is another branch after the else or if, and loop onwards...
            match self.peek() {
                Some(token) if token.has_atom(TokenAtom::Keyword(Keyword::Else)) => {
                    self.skip_token();

                    match self.peek() {
                        Some(token) if token.has_atom(TokenAtom::Keyword(Keyword::If)) => {
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

                    cases.push(
                        self.node_from_location(
                            MatchCase {
                                pattern: self.node(Pattern::Ignore),
                                expr: self.node_from_location(
                                    Expression::new(ExpressionKind::Block(else_branch)),
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
            cases.push(
                self.node(MatchCase {
                    pattern: self.node(Pattern::Ignore),
                    expr: self.node(Expression::new(ExpressionKind::Block(self.node(
                        Block::Body(BodyBlock {
                            statements: row![&self.wall],
                            expr: None,
                        }),
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
    fn parse_arrow(&self) -> ParseResult<()> {
        // map error into 'Expecting '=>' instead of just individual components.
        let err = |loc| ParseError::Parsing {
            message: "Expected an arrow '=>' here.".to_string(),
            src: self.source_location(&loc),
        };

        self.parse_token_atom(TokenAtom::Eq)
            .map_err(|_| err(self.current_location()))?;
        self.parse_token_atom(TokenAtom::Gt)
            .map_err(|_| err(self.current_location()))?;

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
    pub fn parse_let_statement(&self) -> ParseResult<LetStatement<'c>> {
        debug_assert!(matches!(
            self.current_token().kind,
            TokenKind::Atom(TokenAtom::Keyword(Keyword::Let))
        ));

        let pattern = self.parse_pattern()?;

        let bound = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Lt) => Some(self.parse_type_bound()?),
            _ => None,
        };

        let ty = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Colon) => {
                self.skip_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        let value = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Eq) => {
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
        tree: &Row<'c, Token<'c>>,
        span: Location,
    ) -> ParseResult<AstNodes<'c, Pattern<'c>>> {
        let gen = self.from_stream(tree, span);

        gen.parse_separated_fn(
            || gen.parse_pattern(),
            || gen.parse_token_atom(TokenAtom::Comma),
        )
    }

    /// Parse a destructuring pattern. The destructuring pattern refers to destructuring
    /// either a struct or a namespace to extract fields, exported members. The function
    /// takes in a token atom because both syntaxes use different operators as pattern
    /// assigners.
    pub fn parse_destructuring_pattern(
        &self,
        assigning_op: TokenAtom,
    ) -> ParseResult<AstNode<'c, DestructuringPattern<'c>>> {
        let start = self.current_location();
        let name = self.parse_ident()?;

        // if the next token is the correct assigning operator, attempt to parse a
        // pattern here, if not then we copy the parsed ident and make a binding
        // pattern.
        let pattern = match self.peek_resultant_fn(|| self.parse_token_atom(assigning_op)) {
            Some(_) => self.parse_pattern()?,
            None => {
                let copy = self.node(Name { ..*name.body() });
                let loc = copy.location();
                self.node_with_location(Pattern::Binding(copy), loc)
            }
        };

        Ok(self.node_from_joined_location(DestructuringPattern { name, pattern }, &start))
    }

    /// Parse a collection of destructuring patterns that are comma separated.
    pub fn parse_destructuring_patterns(
        &self,
        tree: &Row<'c, Token<'c>>,
        span: Location,
        struct_syntax: bool,
    ) -> ParseResult<AstNodes<'c, DestructuringPattern<'c>>> {
        let gen = self.from_stream(tree, span);

        // Since struct and namespace destructuring patterns use different operators
        // to rename/assign patterns to the specific fields, determine which to use here...
        let renaming_operator = if struct_syntax { TokenAtom::Eq } else { TokenAtom::Colon };

        let mut patterns = row![&self.wall;];

        while gen.has_token() {
            match gen.peek_resultant_fn(|| gen.parse_destructuring_pattern(renaming_operator)) {
                Some(pat) => patterns.push(pat, &self.wall),
                None => break,
            }

            if gen.has_token() {
                gen.parse_token_atom(TokenAtom::Comma)?;
            }
        }

        Ok(patterns)
    }

    /// Parse a singular pattern. Singular patterns cannot have any grouped pattern
    /// operators such as a '|', if guards or any form of compound pattern.
    pub fn parse_singular_pattern(&self) -> ParseResult<AstNode<'c, Pattern<'c>>> {
        let token = self.peek().ok_or(ParseError::Parsing {
            message: "Unexpected eof".to_string(),
            src: self.source_location(&self.current_location()),
        })?;

        let start = self.current_location();

        let pattern = match token {
            Token {
                kind: TokenKind::Atom(TokenAtom::Ident(k)),
                span,
            } => {
                // this could be either just a binding pattern, enum, or a struct pattern
                self.skip_token();

                // So here we try to parse an access name, if it is only made of a single binding
                // name, we'll just return this as a binding pattern, otherwise it must follow that
                // it is either a enum or struct pattern, if not we report it as an error since
                // access names cannot be used as binding patterns on their own...
                let name = self.parse_access_name(k)?;

                match self.peek() {
                    Some(token) if token.is_brace_tree() => {
                        let (tree, span) = self.next_token().unwrap().into_tree();

                        Pattern::Struct(StructPattern {
                            name,
                            entries: self.parse_destructuring_patterns(tree, span, true)?,
                        })
                    }
                    Some(token) if token.is_paren_tree() => {
                        // enum_pattern
                        let (tree, span) = self.next_token().unwrap().into_tree();

                        Pattern::Enum(EnumPattern {
                            name,
                            args: self.parse_pattern_collection(tree, span)?,
                        })
                    }
                    Some(token) if name.path.len() > 1 => self.unexpected_token_error(
                        &token.kind,
                        &TokenKindVector::begin_pattern_collection(&self.wall),
                        &self.current_location(),
                    )?,
                    _ => {
                        // @@Speed: Always performing a lookup?
                        if IDENTIFIER_MAP.ident_name(*k) == "_" {
                            Pattern::Ignore
                        } else {
                            Pattern::Binding(self.node_from_location(Name { ident: *k }, span))
                        }
                    }
                }
            }
            token if token.kind.is_literal() => {
                self.skip_token();
                Pattern::Literal(self.convert_literal_kind_into_pattern(&token.kind))
            }
            token if token.is_paren_tree() => {
                let (tree, span) = self.next_token().unwrap().into_tree();
                // @@Hack: here it might actually be a nested pattern in parenthesees. So we perform a slight
                // transformation if the number of parsed patterns is only one. So essentially we handle the case
                // where a pattern is wrapped in parentheses and so we just unwrap it.
                let mut elements = self.parse_pattern_collection(tree, span)?;

                if elements.len() == 1 {
                    let element = elements.pop().unwrap();
                    return Ok(element);
                } else {
                    Pattern::Tuple(TuplePattern { elements })
                }
            }
            token if token.is_brace_tree() => {
                let (tree, span) = self.next_token().unwrap().into_tree();

                Pattern::Namespace(NamespacePattern {
                    patterns: self.parse_destructuring_patterns(tree, span, false)?,
                })
            }
            // @@Future: List patterns aren't supported yet.
            // Token {kind: TokenKind::Tree(Delimiter::Bracket, tree), span} => {
            //                 self.skip_token();
            //     // this is a list pattern
            //
            // }
            token => self.unexpected_token_error(
                &token.kind,
                &TokenKindVector::begin_pattern(&self.wall),
                &token.span,
            )?,
        };

        Ok(self.node_from_joined_location(pattern, &start))
    }

    /// Parse a block.
    pub fn parse_block(&self) -> ParseResult<AstNode<'c, Block<'c>>> {
        let (gen, start) = match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree),
                span,
            }) => {
                self.skip_token(); // step-along since we matched a block...

                (self.from_stream(tree, self.current_location()), *span)
            }
            Some(token) => self.error(format!(
                "Expected block body, which begins with a '{{' but got a {}",
                token
            ))?,
            // @@ErrorReporting
            None => self
                .error_with_location("Expected block body, which begins with a '{', but reached end of input", &self.next_location())?,
        };

        self.parse_block_from_gen(&gen, start, None)
    }

    /// Function to parse a block body
    pub fn parse_block_from_gen(
        &self,
        gen: &Self,
        start: Location,
        initial_statement: Option<AstNode<'c, Statement<'c>>>,
    ) -> ParseResult<AstNode<'c, Block<'c>>> {
        // Edge case where the statement is parsed and the 'last_statement_is_expr' is set, here
        // we take the expression and return a block that has the expression left here.

        // Append the initial statement if there is one.
        let mut block = if initial_statement.is_some() {
            BodyBlock {
                statements: row![&self.wall; initial_statement.unwrap()],
                expr: None,
            }
        } else {
            BodyBlock {
                statements: row![&self.wall],
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
                block.statements.push(gen.parse_statement()?, &self.wall);
                continue;
            }

            // if we can't tell if this is a statement, we parse an expression, and if there
            // is a following semi-colon, then we make this a statement and continue...
            let expr = gen.parse_expression_with_precedence(0)?;
            let expr_loc = expr.location();

            // check for assigning operators here if the lhs expression is not compound
            match gen.peek_resultant_fn(|| gen.parse_re_assignment_op()) {
                Some(op) => {
                    // transform the operator kind into OperatorFn so we can transform the operator into a function call.
                    let transformed_op: OperatorFn = op.into();

                    // since this is followed by an expression, we try to parse another expression, and then
                    // ensure that after an expression there is a ending semi colon.
                    let rhs = gen.parse_expression_with_precedence(0)?;
                    gen.parse_token_atom(TokenAtom::Semi)?;

                    block.statements.push(
                        gen.node_from_joined_location(
                            Statement::Expr(self.transform_binary_expression(
                                expr,
                                rhs,
                                transformed_op,
                            )),
                            &expr_loc,
                        ),
                        &self.wall,
                    );
                }
                None => {
                    match gen.peek() {
                        Some(token) if token.has_atom(TokenAtom::Semi) => {
                            gen.skip_token();

                            block.statements.push(
                                gen.node_from_joined_location(Statement::Expr(expr), &expr_loc),
                                &self.wall,
                            );
                        }
                        Some(token) if token.has_atom(TokenAtom::Eq) => {
                            gen.skip_token();

                            // Parse the rhs and the semi
                            let rhs = gen.parse_expression_with_precedence(0)?;
                            gen.parse_token_atom(TokenAtom::Semi)?;

                            block.statements.push(
                                gen.node_from_joined_location(
                                    Statement::Assign(AssignStatement { lhs: expr, rhs }),
                                    &start,
                                ),
                                &self.wall,
                            );
                        }
                        Some(token) => {
                            match expr.into_body().move_out().into_kind() {
                                ExpressionKind::Block(inner_block) => block.statements.push(
                                    gen.node_from_joined_location(
                                        Statement::Block(inner_block),
                                        &expr_loc,
                                    ),
                                    &self.wall,
                                ),
                                _ => gen.unexpected_token_error(
                                    &token.kind,
                                    &TokenKindVector::from_row(row![&self.wall; TokenAtom::Semi]),
                                    &gen.current_location(),
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
    pub fn parse_expression(&self) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let token = self.next_token();

        if token.is_none() {
            return self
                .unexpected_eof_with_ctx("Expected the beginning of an expression here.")?;
        }

        let token = token.unwrap();

        // ::CompoundExpressions: firstly, we have to get the initial part of the expression, and then we can check
        // if there are any additional parts in the forms of either property accesses, indexing or infix function calls
        let subject = match &token.kind {
            kind if kind.is_unary_op() => return self.parse_unary_expression(),

            // Handle primitive literals
            kind if kind.is_literal() => self.parse_literal(),
            TokenKind::Atom(TokenAtom::Ident(ident)) => {
                // record the starting span
                let start = self.current_location();

                let (name, type_args) = self.parse_name_with_type_args(ident)?;
                let type_args = type_args.unwrap_or_else(|| row![&self.wall]);

                // create the lhs expr.
                self.node_with_location(
                    Expression::new(ExpressionKind::Variable(VariableExpr { name, type_args })),
                    start.join(self.current_location()),
                )
            }

            // @@Note: This doesn't cover '{' case.
            kind if kind.begins_block() => {
                let start = self.current_location();
                let atom = kind.to_atom();

                let block = match atom {
                    TokenAtom::Keyword(Keyword::For) => self.parse_for_loop()?,
                    TokenAtom::Keyword(Keyword::While) => self.parse_while_loop()?,
                    TokenAtom::Keyword(Keyword::Loop) => {
                        self.node_from_joined_location(Block::Loop(self.parse_block()?), &start)
                    }
                    TokenAtom::Keyword(Keyword::If) => self.parse_if_statement()?,
                    TokenAtom::Keyword(Keyword::Match) => self.parse_match_block()?,
                    _ => unreachable!(),
                };

                self.node_from_joined_location(
                    Expression::new(ExpressionKind::Block(block)),
                    &start,
                )
            }
            // Import
            TokenKind::Atom(TokenAtom::Keyword(Keyword::Import)) => self.parse_import()?,
            // Handle tree literals
            TokenKind::Tree(Delimiter::Brace, tree) => {
                self.parse_block_or_braced_literal(tree, &self.current_location())?
            }
            TokenKind::Tree(Delimiter::Bracket, tree) => {
                self.parse_array_literal(tree, &self.current_location())?
            } // Could be an array index?
            TokenKind::Tree(Delimiter::Paren, tree) => {
                self.disallow_struct_literals.set(true); // @@Cleanup

                // check whether a function return type is following...
                let mut is_func =
                    matches!(self.peek(), Some(token) if token.has_atom(TokenAtom::Colon));

                // Now here we have to look ahead after the token_tree to see if there is an arrow
                if !is_func {
                    // @@Speed: avoid using parse_token_atom() because we don't care about error messages
                    //          We just want to purely look if there are is a combination of symbols following
                    //          which make up an '=>'.
                    let has_arrow = self
                        .peek_resultant_fn(|| -> Result<(), ()> {
                            self.parse_token_atom_fast(TokenAtom::Eq).ok_or(())?;
                            self.parse_token_atom_fast(TokenAtom::Gt).ok_or(())?;
                            Ok(())
                        })
                        .is_some();

                    if has_arrow {
                        self.offset.set(self.offset.get() - 2);
                        is_func = true;
                    }
                }

                match is_func {
                    true => {
                        let gen = self.from_stream(tree, token.span);
                        self.parse_function_literal(&gen)?
                    }
                    false => self.parse_expression_or_tuple(tree, &self.current_location())?,
                }
            }

            TokenKind::Atom(TokenAtom::Keyword(kw)) => {
                return Err(ParseError::Parsing {
                    message: format!("Unexpected keyword '{}' in place of an expression.", kw),
                    src: self.source_location(&token.span),
                })
            }
            kind => {
                return Err(ParseError::Parsing {
                    message: format!("Unexpected token '{}' in the place of an expression.", kind),
                    src: self.source_location(&token.span),
                })
            }
        };

        self.parse_singular_expression(subject)
    }

    /// Provided an initial subject expression that is parsed by the parent caller, this function
    /// will check if there are any additional components to the expression; in the form of either
    /// property access, infix function calls, indexing, etc.
    pub fn parse_singular_expression(
        &self,
        subject: AstNode<'c, Expression<'c>>,
    ) -> ParseResult<AstNode<'c, Expression<'c>>> {
        // record the starting span
        let start = self.current_location();

        let mut lhs_expr = subject;

        // so here we need to peek to see if this is either a index_access, field access or a function call...
        while let Some(next_token) = self.peek() {
            match &next_token.kind {
                // Property access or infix function call
                TokenKind::Atom(TokenAtom::Dot) => {
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
                            args.entries.insert(0, lhs_expr, &self.wall);

                            lhs_expr = AstNode::new(
                                Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                                    subject,
                                    args,
                                })),
                                start.join(self.current_location()),
                                &self.wall,
                            );
                        }
                        ExpressionKind::Variable(VariableExpr { name, type_args: _ }) => {
                            // @@Cleanup: This produces an AstNode<AccessName> whereas we just want the single name...
                            let location = name.location();
                            let ident = name.body().path.get(0).unwrap();

                            let node = self.node_with_location(Name { ident: *ident }, location);

                            lhs_expr = AstNode::new(
                                Expression::new(ExpressionKind::PropertyAccess(
                                    PropertyAccessExpr {
                                        subject: lhs_expr,
                                        property: node,
                                    },
                                )),
                                start.join(self.current_location()),
                                &self.wall,
                            );
                        }
                        _ => {
                            return Err(ParseError::Parsing {
                                message: "Expected field name or an infix function call"
                                    .to_string(),
                                src: self.source_location(&self.current_location()),
                            })
                        }
                    }
                }
                // Array index access syntax: ident[...]
                TokenKind::Tree(Delimiter::Bracket, tree) => {
                    self.skip_token();
                    lhs_expr = self.parse_array_index(lhs_expr, tree, self.current_location())?;
                }
                // Function call
                TokenKind::Tree(Delimiter::Paren, tree) => {
                    self.skip_token();
                    lhs_expr = self.parse_function_call(lhs_expr, tree, self.current_location())?;
                }
                // Struct literal
                TokenKind::Tree(Delimiter::Brace, tree) if !self.disallow_struct_literals.get() => {
                    self.skip_token();
                    // Ensure that the LHS of the brace is a variable, since struct literals can only
                    // be begun with variable names and type arguments, any other expression cannot be
                    // the beginning of a struct literal.

                    let location = lhs_expr.location();
                    lhs_expr = match lhs_expr.into_body().move_out().into_kind() {
                        ExpressionKind::Variable(VariableExpr { name, type_args }) => {
                            self.parse_struct_literal(name, type_args, tree)?
                        }
                        expr => AstNode::new(Expression::new(expr), location, &self.wall),
                    };
                }
                _ => break,
            }
        }

        // reset disallowing struct literals
        self.disallow_struct_literals.set(false);

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
    pub fn parse_import(&self) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let start = self.current_location();

        let (tree, span) = match self.peek() {
            Some(token) if token.is_paren_tree() => token.into_tree(),
            Some(token) => self.unexpected_token_error(
                &token.kind,
                &TokenKindVector::from_row(
                    row![&self.wall; TokenAtom::Delimiter(Delimiter::Paren, true)],
                ),
                &self.current_location(),
            )?,
            None => self.unexpected_eof()?,
        };

        let gen = self.from_stream(tree, span);

        let (raw, path, span) = match gen.peek() {
            Some(Token {
                kind: TokenKind::Atom(TokenAtom::StrLiteral(str)),
                span,
            }) => (str, STRING_LITERAL_MAP.lookup(*str), span),
            _ => gen.error("Expected an import path.")?,
        };

        gen.skip_token(); // eat the string argument

        if gen.has_token() {
            gen.expected_eof()?;
        }

        let module_idx = self
            .resolver
            .add_module(path, Some(self.source_location(span)))?;

        Ok(self.node_from_joined_location(
            Expression::new(ExpressionKind::Import(self.node_from_joined_location(
                Import {
                    path: *raw,
                    index: module_idx,
                },
                &start,
            ))),
            &start,
        ))
    }

    /// Parse a function call which requires that the [AccessName] is pre-parsed and passed
    /// into the function which deals with the call arguments.
    pub fn parse_function_call(
        &self,
        ident: AstNode<'c, Expression<'c>>,
        tree: &Row<'c, Token<'c>>,
        span: Location,
    ) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, span);
        let mut args = AstNode::new(
            FunctionCallArgs {
                entries: row![&self.wall],
            },
            span,
            &self.wall,
        );

        while gen.has_token() {
            let arg = gen.parse_expression_with_precedence(0);
            args.entries.push(arg?, &self.wall);

            // now we eat the next token, checking that it is a comma
            match gen.peek() {
                Some(token) if token.has_atom(TokenAtom::Comma) => gen.next_token(),
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
    pub fn parse_token_atom_fast(&self, atom: TokenAtom) -> Option<()> {
        match self.peek() {
            Some(token) if token.has_atom(atom) => {
                self.skip_token();
                Some(())
            }
            _ => None,
        }
    }

    /// Function to parse the next token with the same kind as the specified kind, this
    /// is a useful utility function for parsing singular tokens in the place of more complex
    /// compound statements and expressions.
    pub fn parse_token_atom(&self, atom: TokenAtom) -> ParseResult<()> {
        match self.peek() {
            Some(token) if token.has_atom(atom) => {
                self.skip_token();
                Ok(())
            }
            Some(token) => Err(ParseError::Parsing {
                message: format!("Expected a '{}', but got a '{}'", atom, token.kind),
                src: self.source_location(&token.span),
            }),
            _ => Err(ParseError::Parsing {
                message: format!("Expected a '{}', but reached end of input", atom),
                src: self.source_location(&self.current_location()),
            }),
        }
    }

    /// Parse a struct literal.
    pub fn parse_struct_literal(
        &self,
        name: AstNode<'c, AccessName<'c>>,
        type_args: Row<'c, AstNode<'c, Type<'c>>>,
        tree: &Row<'c, Token<'c>>,
    ) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let start = self.current_location();
        let gen = self.from_stream(tree, start);

        let mut entries = row![&self.wall];

        while gen.has_token() {
            let entry_start = gen.current_location();

            let name = gen.parse_ident()?;
            gen.parse_token_atom(TokenAtom::Eq)?;
            let value = gen.parse_expression_with_precedence(0)?;

            entries.push(
                gen.node_with_location(
                    StructLiteralEntry { name, value },
                    entry_start.join(gen.current_location()),
                ),
                &self.wall,
            );

            // now we eat the next token, checking that it is a comma
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Atom(TokenAtom::Comma)) => {
                    gen.next_token()
                }
                _ => break,
            };
        }

        Ok(self.node_from_joined_location(
            Expression::new(ExpressionKind::LiteralExpr(self.node_from_joined_location(
                Literal::Struct(StructLiteral {
                    name,
                    type_args,
                    entries,
                }),
                &start,
            ))),
            &start,
        ))
    }

    /// Parse an array index. Array indexes are constructed with square brackets
    /// wrapping a singular expression.
    pub fn parse_array_index(
        &self,
        ident: AstNode<'c, Expression<'c>>,
        tree: &Row<'c, Token<'c>>,
        span: Location,
    ) -> ParseResult<AstNode<'c, Expression<'c>>> {
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
                        entries: row![&self.wall; ident, index_expr],
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
    pub fn parse_unary_expression(&self) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let token = self.current_token();
        let start = self.current_location();

        let expr_kind = match &token.kind {
            TokenKind::Atom(TokenAtom::Star) => ExpressionKind::Deref(self.parse_expression()?),
            TokenKind::Atom(TokenAtom::Amp) => {
                // Check if this reference is raw...
                match self.peek() {
                    Some(token) if token.has_atom(TokenAtom::Keyword(Keyword::Raw)) => {
                        self.skip_token();
                        ExpressionKind::Ref(self.parse_expression()?, RefKind::Raw)
                    }
                    _ => ExpressionKind::Ref(self.parse_expression()?, RefKind::Normal),
                }
            }
            kind @ (TokenKind::Atom(TokenAtom::Plus) | TokenKind::Atom(TokenAtom::Minus)) => {
                let expr = self.parse_expression()?;
                let loc = expr.location();

                let fn_name = match kind {
                    TokenKind::Atom(TokenAtom::Plus) => "pos",
                    TokenKind::Atom(TokenAtom::Minus) => "neg",
                    _ => unreachable!(),
                };

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident(fn_name, &start),
                    args: self.node_from_location(
                        FunctionCallArgs {
                            entries: row![&self.wall; expr],
                        },
                        &loc,
                    ),
                })
            }
            TokenKind::Atom(TokenAtom::Tilde) => {
                let arg = self.parse_expression()?;
                let loc = arg.location();

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident("notb", &start),
                    args: self.node_from_location(
                        FunctionCallArgs {
                            entries: row![&self.wall; arg],
                        },
                        &loc,
                    ),
                })
            }
            TokenKind::Atom(TokenAtom::Hash) => {
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
            TokenKind::Atom(TokenAtom::Exclamation) => {
                let arg = self.parse_expression()?;
                let loc = arg.location();

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident("not", &start),
                    args: self.node_from_location(
                        FunctionCallArgs {
                            entries: row![&self.wall; arg],
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
    ) -> ParseResult<(AstNode<'c, AccessName<'c>>, AstNodes<'c, Type<'c>>)> {
        let name = self.parse_access_name(ident)?;
        let args = self.parse_type_args()?;

        Ok((name, args))
    }

    /// Parse an access name followed by optional type arguments..
    pub fn parse_name_with_type_args(
        &self,
        ident: &Identifier,
    ) -> ParseResult<(AstNode<'c, AccessName<'c>>, Option<AstNodes<'c, Type<'c>>>)> {
        let name = self.parse_access_name(ident)?;

        // @@Speed: so here we want to be efficient about type_args, we'll just try to
        // see if the next token atom is a 'Lt' rather than using parse_token_atom
        // because it throws an error essentially and thus allocates a stupid amount
        // of strings which at the end of the day aren't even used...
        let args = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Lt) => {
                self.peek_resultant_fn(|| self.parse_type_args())
            }
            _ => None,
        };

        Ok((name, args))
    }

    /// Parses a single identifier, essentially converting the current [TokenAtom::Ident] into
    /// an [AstNode<Name>], assuming that the next token is an identifier.
    pub fn parse_ident(&self) -> ParseResult<AstNode<'c, Name>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Atom(TokenAtom::Ident(ident)),
                span,
            }) => {
                self.skip_token();

                Ok(AstNode::new(Name { ident: *ident }, *span, &self.wall))
            }
            Some(token) => self.unexpected_token_error(
                &token.kind,
                &TokenKindVector::from_row(row![&self.wall; TokenAtom::GenericIdent]),
                &self.current_location(),
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
    ) -> ParseResult<AstNode<'c, AccessName<'c>>> {
        let start = self.current_location();
        let mut path = row![&self.wall; *start_id];

        loop {
            match self.peek() {
                Some(token) if token.has_atom(TokenAtom::Colon) => {
                    self.skip_token(); // :

                    match self.peek() {
                        Some(token) if token.has_atom(TokenAtom::Colon) => {
                            self.skip_token(); // :

                            match self.peek() {
                                Some(Token {
                                    kind: TokenKind::Atom(TokenAtom::Ident(id)),
                                    span: _,
                                }) => {
                                    self.skip_token();
                                    path.push(*id, &self.wall);
                                }
                                _ => {
                                    return Err(ParseError::Parsing {
                                        message: "Expected identifier after a name access"
                                            .to_string(),
                                        src: self.source_location(&self.current_location()),
                                    })
                                }
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
    ) -> ParseResult<AstNode<'c, BodyBlock<'c>>> {
        Ok(AstNode::new(
            BodyBlock {
                statements: row![&self.wall],
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
    ) -> ParseResult<AstNode<'c, Expression<'c>>> {
        // first of all, we want to get the lhs...
        let mut lhs = self.parse_expression()?;

        // reset the compound_expr flag, since this is a new expression...
        self.is_compound_expr.set(false);

        loop {
            let op_start = self.current_location();
            // this doesn't consider operators that have an 'eq' variant because that is handled at the statement level,
            // since it isn't really a binary operator...
            let (op, consumed_tokens) = Operator::from_token_stream(self);

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
                        let transformed_op: OperatorFn = op.into();
                        lhs = self.transform_binary_expression(lhs, rhs, transformed_op);
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
    pub fn parse_type_args(&self) -> ParseResult<AstNodes<'c, Type<'c>>> {
        self.parse_token_atom(TokenAtom::Lt)?;
        let mut type_args = row![&self.wall];

        loop {
            // Check if the type argument is parsed, if we have already encountered a comma, we
            // return a hard error because it has already started on a comma.
            match self.parse_type() {
                Ok(ty) => type_args.push(ty, &self.wall),
                Err(err) => return Err(err),
            };

            // Now consider if the bound is closing or continuing with a comma...
            match self.peek() {
                Some(token) if token.has_atom(TokenAtom::Comma) => {
                    self.skip_token();
                }
                Some(token) if token.has_atom(TokenAtom::Gt) => {
                    self.skip_token();
                    break;
                }
                Some(token) => self.unexpected_token_error(
                    &token.kind,
                    &TokenKindVector::from_row(row![&self.wall; TokenAtom::Comma, TokenAtom::Gt]),
                    &self.current_location(),
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
    ) -> ParseResult<AstNode<'c, Type<'c>>> {
        let start = self.current_location();

        let mut type_args = row![&self.wall; ];

        // handle the function arguments first by checking for parentheses
        match self.peek() {
            Some(token) if token.is_paren_tree() => {
                self.skip_token();

                let (tree, span) = token.into_tree();
                let gen = self.from_stream(tree, span);

                match gen.peek() {
                    // Handle special case where there is only one comma and no following items...
                    // Special edge case for '(,)' or an empty tuple type...
                    Some(token) if token.has_atom(TokenAtom::Comma) && gen.stream.len() == 1 => {
                        gen.skip_token();
                    }
                    _ => {
                        type_args = gen.parse_separated_fn(
                            || gen.parse_type(),
                            || gen.parse_token_atom(TokenAtom::Comma),
                        )?;
                    }
                };
            }
            Some(token) => self.unexpected_token_error(
                &token.kind,
                &TokenKindVector::from_row(
                    row![&self.wall; TokenAtom::Delimiter(Delimiter::Paren, false)],
                ),
                &self.current_location(),
            )?,
            None => self.unexpected_eof()?,
        };

        // If there is an arrow '=>', then this must be a function type
        let name = match self.peek_resultant_fn(|| self.parse_arrow()) {
            Some(_) => {
                // Parse the return type here, and then give the function name
                type_args.push(self.parse_type()?, &self.wall);
                IDENTIFIER_MAP.create_ident(FUNCTION_TYPE_NAME)
            }
            None => {
                if must_be_function {
                    self.error(
                        "Expected an arrow '=>' after type arguments denoting a function type.",
                    )?;
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
    pub fn parse_type(&self) -> ParseResult<AstNode<'c, Type<'c>>> {
        let start = self.current_location();
        let token = self
            .peek()
            .ok_or_else(|| self.unexpected_eof::<()>().err().unwrap())?;

        let variant = match &token.kind {
            TokenKind::Atom(TokenAtom::Amp) => {
                self.skip_token();

                // Check if this is a raw ref by checking if the keyword is present...
                let is_ref = match self.peek() {
                    Some(token) if token.has_atom(TokenAtom::Keyword(Keyword::Raw)) => {
                        self.skip_token();
                        true
                    }
                    _ => false,
                };

                match self.parse_type() {
                    Ok(ty) if is_ref => Type::RawRef(ty),
                    Ok(ty) => Type::Ref(ty),
                    err => return err,
                }
            }
            TokenKind::Atom(TokenAtom::Question) => {
                self.skip_token();
                Type::Existential
            }
            TokenKind::Atom(TokenAtom::Ident(id)) => {
                self.skip_token();

                let (name, args) = self.parse_name_with_type_args(id)?;
                // if the type_args are None, this means that the name could be either a
                // infer_type, or a type_var...
                match args {
                    Some(type_args) => Type::Named(NamedType { name, type_args }),
                    None => {
                        // @@Cleanup: This produces an AstNode<AccessName> whereas we just want the single name...
                        let location = name.location();
                        let ident = name.body().path.get(0).unwrap();

                        match IDENTIFIER_MAP.ident_name(*ident) {
                            "_" => Type::Infer,
                            // ##TypeArgsNaming: Here the rules are built-in for what the name of a type-arg is,
                            //                   a capital character of length 1...
                            ident_name => {
                                if ident_name.len() == 1
                                    && ident_name.chars().all(|x| x.is_ascii_uppercase())
                                {
                                    let name =
                                        self.node_with_location(Name { ident: *ident }, location);

                                    Type::TypeVar(TypeVar { name })
                                } else {
                                    Type::Named(NamedType {
                                        name,
                                        type_args: row![&self.wall],
                                    })
                                }
                            }
                        }
                    }
                }
            }

            // Map or set type
            TokenKind::Tree(Delimiter::Brace, tree) => {
                self.skip_token();

                let gen = self.from_stream(tree, token.span);

                let lhs_type = gen.parse_type()?;

                match gen.peek() {
                    // This must be a map
                    Some(token) if token.has_atom(TokenAtom::Colon) => {
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
                            type_args: row![&self.wall; lhs_type, rhs_type],
                        })
                    }
                    Some(_) => gen.expected_eof()?,
                    None => {
                        // @@Incomplete: inline type names into ident map...
                        let name = IDENTIFIER_MAP.create_ident(SET_TYPE_NAME);

                        Type::Named(NamedType {
                            name: self.make_access_name_from_identifier(name, token.span),
                            type_args: row![&self.wall; lhs_type],
                        })
                    }
                }
            }

            // List type
            TokenKind::Tree(Delimiter::Bracket, tree) => {
                self.skip_token();

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
                    type_args: row![&self.wall; inner_type],
                })
            }

            // Tuple or function type
            TokenKind::Tree(Delimiter::Paren, _) => self
                .parse_function_or_tuple_type(false)?
                .into_body()
                .move_out(),
            _ => {
                return Err(ParseError::Parsing {
                    message: "Expected type here.".to_string(),
                    src: self.source_location(&self.current_location()),
                })
            }
        };

        Ok(self.node_from_joined_location(variant, &start))
    }

    /// Parse an single name or a function call that is applied on the left hand side
    /// expression. Infix calls and name are only separated by infix calls having
    /// parenthesees at the end of the name.
    pub fn parse_name_or_infix_call(&self) -> ParseResult<AstNode<'c, Expression<'c>>> {
        debug_assert!(self.current_token().has_atom(TokenAtom::Dot));

        let start = self.current_location();

        match &self.next_token() {
            Some(Token {
                kind: TokenKind::Atom(TokenAtom::Ident(id)),
                span: id_span,
            }) => match self.peek() {
                Some(Token {
                    kind: TokenKind::Tree(Delimiter::Paren, stream),
                    span,
                }) => {
                    // Eat the generator now...
                    self.skip_token();

                    // @@Parallelisable: Since this is a vector of tokens, we should be able to give the resolver, create a new
                    //                   generator and form function call arguments from the stream...
                    let mut args = self.node_with_location(
                        FunctionCallArgs {
                            entries: row![&self.wall],
                        },
                        *span,
                    );

                    // so we know that this is the beginning of the function call, so we have to essentially parse an arbitrary number
                    // of expressions separated by commas as arguments to the call.

                    let gen = self.from_stream(stream, *span);

                    while gen.has_token() {
                        let arg = gen.parse_expression_with_precedence(0);
                        args.entries.push(arg?, &self.wall);

                        // now we eat the next token, checking that it is a comma
                        match gen.peek() {
                            Some(token) if token.has_atom(TokenAtom::Comma) => gen.next_token(),
                            _ => break,
                        };
                    }

                    Ok(self.node_with_location(
                        Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                            subject: self.make_variable_from_identifier(*id, *id_span),
                            args,
                        })),
                        start.join(self.current_location()),
                    ))
                }
                _ => Ok(self.make_variable_from_identifier(*id, *id_span)),
            },
            _ => self.error("Expecting field name after property access.")?,
        }
    }

    /// Parse either a block, a set, or a map. The function has to parse
    /// an initial expression and then determine the type of needed parsing
    /// by the following operator, whether it is a colon, comma or a semicolon.
    pub fn parse_block_or_braced_literal(
        &self,
        tree: &Row<'c, Token<'c>>,
        span: &Location,
    ) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, *span);

        // handle two special cases for empty map and set literals, if the only token
        // is a colon, this must be a map literal, or if the only token is a comma it is
        // an empty set literal.
        if gen.stream.len() == 1 {
            match gen.peek().unwrap() {
                token if token.has_atom(TokenAtom::Colon) => {
                    return Ok(self.node_from_location(
                        Expression::new(ExpressionKind::LiteralExpr(self.node_from_location(
                            Literal::Map(MapLiteral {
                                elements: row![&self.wall],
                            }),
                            span,
                        ))),
                        span,
                    ))
                }
                token if token.has_atom(TokenAtom::Comma) => {
                    return Ok(self.node_from_location(
                        Expression::new(ExpressionKind::LiteralExpr(self.node_from_location(
                            Literal::Set(SetLiteral {
                                elements: row![&self.wall],
                            }),
                            span,
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
                Expression::new(ExpressionKind::Block(self.node_from_location(
                    Block::Body(BodyBlock {
                        statements: row![&self.wall],
                        expr: None,
                    }),
                    span,
                ))),
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
        let initial_statement = gen.parse_statement()?;
        let location = initial_statement.location();
        let initial_statement = initial_statement.into_body().move_out();

        match (gen.peek(), initial_statement) {
            (Some(token), Statement::Expr(initial_expr)) if token.has_atom(TokenAtom::Comma) => {
                gen.skip_token(); // ','

                let literal = self.parse_set_literal(gen, initial_expr)?;

                Ok(self.node_from_location(
                    Expression::new(ExpressionKind::LiteralExpr(literal)),
                    span,
                ))
            }
            (Some(token), Statement::Expr(initial_expr)) if token.has_atom(TokenAtom::Colon) => {
                gen.skip_token(); // ':'

                let start_pos = initial_expr.location();
                let entry = self.node_from_joined_location(
                    MapLiteralEntry {
                        key: initial_expr,
                        value: gen.parse_expression_with_precedence(0)?,
                    },
                    &start_pos,
                );

                // Peek ahead to check if there is a comma, if there is then we'll parse more map entries,
                // and pass it into parse_map_literal.
                match gen.peek() {
                    Some(token) if token.has_atom(TokenAtom::Comma) => {
                        gen.skip_token();

                        let literal = self.parse_map_literal(gen, entry)?;

                        Ok(self.node_from_location(
                            Expression::new(ExpressionKind::LiteralExpr(literal)),
                            span,
                        ))
                    }
                    _ => Ok(self.node_from_location(
                        Expression::new(ExpressionKind::LiteralExpr(self.node_from_location(
                            Literal::Map(MapLiteral {
                                elements: row![&self.wall; entry],
                            }),
                            span,
                        ))),
                        span,
                    )),
                }
            }
            (Some(_), statement) => {
                let statement = self.node_with_location(statement, location);

                // check here if there is a 'semi', and then convert the expression into a statement.
                let block = self.parse_block_from_gen(&gen, *span, Some(statement))?;

                Ok(self.node_from_location(Expression::new(ExpressionKind::Block(block)), span))
            }
            (None, Statement::Expr(initial_expr)) => {
                // This block is just a block with a single expression

                Ok(self.node_from_location(
                    Expression::new(ExpressionKind::Block(self.node_from_location(
                        Block::Body(BodyBlock {
                            statements: row![&self.wall],
                            expr: Some(initial_expr),
                        }),
                        span,
                    ))),
                    span,
                ))
            }
            (None, statement) => Ok(self.node_from_location(
                Expression::new(ExpressionKind::Block(self.node_from_location(
                    Block::Body(BodyBlock {
                        statements: row![&self.wall; self.node_with_location(statement, location)],
                        expr: None,
                    }),
                    span,
                ))),
                span,
            )),
        }
    }

    /// Parse a single map entry in a literal.
    pub fn parse_map_entry(&self) -> ParseResult<AstNode<'c, MapLiteralEntry<'c>>> {
        let start = self.current_location();

        let key = self.parse_expression_with_precedence(0)?;
        self.parse_token_atom(TokenAtom::Colon)?;
        let value = self.parse_expression_with_precedence(0)?;

        Ok(self.node_from_joined_location(MapLiteralEntry { key, value }, &start))
    }

    /// Parse a map literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub fn parse_map_literal(
        &self,
        gen: Self,
        initial_entry: AstNode<'c, MapLiteralEntry<'c>>,
    ) -> ParseResult<AstNode<'c, Literal<'c>>> {
        let start = gen.current_location();
        let mut elements = gen.parse_separated_fn(
            || gen.parse_map_entry(),
            || gen.parse_token_atom(TokenAtom::Comma),
        )?;

        elements.insert(0, initial_entry, &self.wall);

        Ok(self.node_from_joined_location(Literal::Map(MapLiteral { elements }), &start))
    }

    /// Parse a set literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub fn parse_set_literal(
        &self,
        gen: Self,
        initial_entry: AstNode<'c, Expression<'c>>,
    ) -> ParseResult<AstNode<'c, Literal<'c>>> {
        let start = self.current_location();

        let mut elements = gen.parse_separated_fn(
            || gen.parse_expression_with_precedence(0),
            || gen.parse_token_atom(TokenAtom::Comma),
        )?;

        // insert the first item into elements
        elements.insert(0, initial_entry, &self.wall);

        Ok(self.node_from_joined_location(Literal::Set(SetLiteral { elements }), &start))
    }

    /// Parse a pattern with an optional if guard after the singular pattern.
    pub fn parse_pattern_with_if(&self) -> ParseResult<AstNode<'c, Pattern<'c>>> {
        let start = self.current_location();
        let pattern = self.parse_singular_pattern()?;

        match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Keyword(Keyword::If)) => {
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
    pub fn parse_pattern(&self) -> ParseResult<AstNode<'c, Pattern<'c>>> {
        let start = self.current_location();

        // Parse the first pattern, but throw away the location information since that will be
        // computed at the end anyway...
        let mut patterns = row![&self.wall;];

        while self.has_token() {
            let pattern = self.parse_pattern_with_if()?;
            patterns.push(pattern, &self.wall);

            // Check if this is going to be another pattern following the current one.
            match self.peek() {
                Some(token) if token.has_atom(TokenAtom::Pipe) => {
                    self.skip_token();
                }
                _ => break,
            }
        }

        // if the length of patterns is greater than one, we return an 'OR' pattern,
        // otherwise just the first pattern.
        if patterns.len() == 1 {
            let pat = patterns.pop().unwrap();
            Ok(pat)
        } else {
            Ok(self
                .node_from_joined_location(Pattern::Or(OrPattern { variants: patterns }), &start))
        }
    }

    /// Parse a function definition argument, which is made of an identifier and a function type.
    pub fn parse_function_def_arg(&self) -> ParseResult<AstNode<'c, FunctionDefArg<'c>>> {
        let start = self.current_location();
        let name = self.parse_ident()?;

        // @@Future: default values for argument...
        let ty = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Colon) => {
                self.skip_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        Ok(self.node_from_joined_location(FunctionDefArg { name, ty }, &start))
    }

    /// Parse a function literal. Function literals are essentially definitions of lambdas
    /// that can be assigned to variables or passed as arguments into other functions.
    pub fn parse_function_literal(&self, gen: &Self) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let start = self.current_location();

        // parse function definition arguments.
        let args = gen.parse_separated_fn(
            || gen.parse_function_def_arg(),
            || gen.parse_token_atom(TokenAtom::Comma),
        )?;

        // check if there is a return type
        let return_ty = match self.peek_resultant_fn(|| self.parse_token_atom(TokenAtom::Colon)) {
            Some(_) => Some(self.parse_type()?),
            _ => None,
        };

        self.parse_arrow()?;

        let fn_body = match self.peek() {
            Some(_) => self.parse_expression_with_precedence(0)?,
            None => self.error("Expected function body here.")?,
        };

        Ok(self.node_from_joined_location(
            Expression::new(ExpressionKind::LiteralExpr(gen.node_from_joined_location(
                Literal::Function(FunctionDef {
                    args,
                    return_ty,
                    fn_body,
                }),
                &start,
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
        tree: &Row<'c, Token<'c>>,
        span: &Location,
    ) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, *span);
        let start = self.current_location();

        // Handle the empty tuple case
        if gen.stream.len() == 1 {
            match gen.peek().unwrap() {
                token if token.has_atom(TokenAtom::Comma) => {
                    gen.skip_token();

                    return Ok(gen.node_from_joined_location(
                        Expression::new(ExpressionKind::LiteralExpr(
                            gen.node_from_joined_location(
                                Literal::Tuple(TupleLiteral {
                                    elements: row![&self.wall;],
                                }),
                                &start,
                            ),
                        )),
                        &start,
                    ));
                }
                _ => (),
            };
        }

        let expr = gen.parse_expression_with_precedence(0)?;

        // Check if this is just a singularly wrapped expression
        if gen.peek().is_none() {
            return Ok(expr);
        }

        let mut elements = row![&self.wall; expr];

        loop {
            match gen.peek() {
                Some(token) if token.has_atom(TokenAtom::Comma) => {
                    gen.skip_token();

                    // Handles the case where this is a trailing comma and no tokens after...
                    if !gen.has_token() {
                        break;
                    }

                    elements.push(gen.parse_expression_with_precedence(0)?, &self.wall)
                }
                Some(_) => {
                    return Err(ParseError::Parsing {
                        message: "Unexpected expression in place of a comma.".to_string(),
                        src: gen.source_location(&start),
                    });
                }
                None => break,
            }
        }

        Ok(gen.node_from_joined_location(
            Expression::new(ExpressionKind::LiteralExpr(gen.node_from_joined_location(
                Literal::Tuple(TupleLiteral { elements }),
                &start,
            ))),
            &start,
        ))
    }

    /// Parse an array literal.
    pub fn parse_array_literal(
        &self,
        tree: &Row<'c, Token<'c>>,
        span: &Location,
    ) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, *span);
        let start = gen.current_location();

        let mut elements = row![&self.wall];

        while gen.has_token() {
            let expr = gen.parse_expression_with_precedence(0)?;
            elements.push(expr, &self.wall);

            match gen.peek() {
                Some(token) if token.has_atom(TokenAtom::Comma) => {
                    gen.skip_token();
                }
                Some(token) => {
                    // if we haven't exhausted the whole token stream, then report this as a unexpected
                    // token error
                    return self.error_with_location(
                        format!(
                            "Unexpected token '{}' in the place of an comma.",
                            token.kind
                        ),
                        &gen.current_location(),
                    );
                }
                None => break,
            }
        }

        Ok(gen.node_from_joined_location(
            Expression::new(ExpressionKind::LiteralExpr(gen.node_from_joined_location(
                Literal::List(ListLiteral { elements }),
                &start,
            ))),
            &start,
        ))
    }

    /// Convert a literal kind into a pattern literal kind.
    pub fn convert_literal_kind_into_pattern(&self, kind: &TokenKind) -> LiteralPattern {
        match kind {
            TokenKind::Atom(TokenAtom::StrLiteral(s)) => LiteralPattern::Str(*s),
            TokenKind::Atom(TokenAtom::CharLiteral(s)) => LiteralPattern::Char(*s),
            TokenKind::Atom(TokenAtom::IntLiteral(s)) => LiteralPattern::Int(*s),
            TokenKind::Atom(TokenAtom::FloatLiteral(s)) => LiteralPattern::Float(*s),
            _ => unreachable!(),
        }
    }

    /// Convert the current token (provided it is a primitive literal) into a [ExpressionKind::LiteralExpr]
    /// by simply matching on the type of the expr.
    pub fn parse_literal(&self) -> AstNode<'c, Expression<'c>> {
        let token = self.current_token();
        let literal = AstNode::new(
            match token.kind {
                TokenKind::Atom(TokenAtom::IntLiteral(num)) => Literal::Int(num),
                TokenKind::Atom(TokenAtom::FloatLiteral(num)) => Literal::Float(num),
                TokenKind::Atom(TokenAtom::CharLiteral(ch)) => Literal::Char(ch),
                TokenKind::Atom(TokenAtom::StrLiteral(str)) => Literal::Str(str),
                _ => unreachable!(),
            },
            token.span,
            &self.wall,
        );

        self.node_from_location(
            Expression::new(ExpressionKind::LiteralExpr(literal)),
            &token.span,
        )
    }
}
