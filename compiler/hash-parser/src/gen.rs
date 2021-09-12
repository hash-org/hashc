//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

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
    resolve::ModuleResolver,
};

use crate::token::TokenAtom;
use crate::{
    operator::Operator,
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

    pub fn generate_module(&mut self) -> ParseResult<Module<'c>> {
        Ok(Module {
            contents: row![&self.wall],
        })
    }

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

    #[inline(always)]
    pub(crate) fn offset(&self) -> usize {
        self.offset.get()
    }

    /// Function to peek at the nth token ahead of the current offset.
    pub(crate) fn peek_nth(&self, at: usize) -> Option<&Token<'c>> {
        self.stream.get(self.offset.get() + at)
    }

    pub(crate) fn peek(&self) -> Option<&Token<'c>> {
        self.peek_nth(0)
    }

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

    /// Function that increases the offset of the next token
    pub(crate) fn next_token(&self) -> Option<&Token<'c>> {
        let value = self.stream.get(self.offset.get());

        if value.is_some() {
            // @@Dumbness: because Cell::update is unsafe
            self.offset.set(self.offset.get() + 1);
        }

        value
    }

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

    /// Create a new [AstNode] from the information provided by the [AstGen]
    pub fn node<T>(&self, inner: T) -> AstNode<'c, T> {
        AstNode::new(inner, self.current_location(), &self.wall)
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    pub fn node_with_location<T>(&self, inner: T, location: Location) -> AstNode<'c, T> {
        AstNode::new(inner, location, &self.wall)
    }

    fn copy_name_node(&self, name: &AstNode<Name>) -> AstNode<'c, Name> {
        self.node(Name { ..*name.body() })
    }

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
    pub(crate) fn unexpected_eof_with_ctx<T>(&self, ctx: &str) -> ParseResult<T> {
        self.error(format!(
            "{}: but unexpectedly reached the end of file.",
            ctx
        ))
    }

    pub(crate) fn make_ident(
        &self,
        name: &str,
        location: &Location,
    ) -> AstNode<'c, Expression<'c>> {
        AstNode::new(
            Expression::new(ExpressionKind::Variable(VariableExpr {
                name: self.node_from_joined_location(
                    AccessName {
                        path: row![&self.wall; IDENTIFIER_MAP.create_ident(name)],
                    },
                    location,
                ),
                type_args: row![&self.wall],
            })),
            *location,
            &self.wall,
        )
    }

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

    pub(crate) fn make_access_name(
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

    /// Make a [AstNode<Name>] from an identifier and provided span.
    pub(crate) fn make_name_from_id(
        &self,
        id: &Identifier,
        location: &Location,
    ) -> AstNode<'c, Name> {
        AstNode::new(Name { ident: *id }, *location, &self.wall)
    }

    pub(crate) fn make_ident_from_id(
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

    pub(crate) fn make_ident_from_op(
        &self,
        op: Operator,
        location: &Location,
    ) -> AstNode<'c, Expression<'c>> {
        self.make_ident(op.as_str(), location)
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
    pub fn peek_resultant_fn<T>(&self, parse_fn: impl Fn() -> ParseResult<T>) -> Option<T> {
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

    pub fn parse_statement(&self) -> ParseResult<AstNode<'c, Statement<'c>>> {
        let start = self.current_location();

        match self.peek() {
            Some(Token { kind, span: _ }) if kind.begins_statement() => {
                self.next_token();

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
                            Some(_) => Statement::Return(Some(self.parse_expression_bp(0)?)),
                            None => Statement::Return(None),
                        }
                    }
                    _ => unreachable!(),
                };

                match self.next_token() {
                    Some(token) if token.has_atom(TokenAtom::Semi) => Ok(AstNode::new(
                        statement,
                        start.join(self.current_location()),
                        &self.wall,
                    )),
                    Some(token) => self.error(format!(
                        "Expecting ';' at the end of a statement, but got '{}' ",
                        token.kind
                    )),
                    None => self.unexpected_eof_with_ctx("Expecting ';' ending a statement.")?,
                }
            }
            Some(_) => {
                let expr = self.parse_expression_bp(0)?;

                // Ensure that the next token is a Semi
                match self.peek() {
                    Some(token) if token.has_atom(TokenAtom::Semi) => {
                        self.next_token();
                        Ok(self.node_from_location(Statement::Expr(expr), &start))
                    }
                    Some(token) if token.has_atom(TokenAtom::Eq) => {
                        self.next_token();

                        // Parse the rhs and the semi
                        let rhs = self.parse_expression_bp(0)?;
                        self.parse_token_atom(TokenAtom::Semi)?;

                        Ok(self.node_from_joined_location(
                            Statement::Assign(AssignStatement { lhs: expr, rhs }),
                            &start,
                        ))
                    }
                    token => match (token, expr.into_body().move_out().into_kind()) {
                        (_, ExpressionKind::Block(block)) => {
                            Ok(self.node_from_location(Statement::Block(block), &start))
                        }
                        (Some(token), _) => self.error(format!(
                            "Expecting ';' at the end of a statement, but got '{}' ",
                            token.kind
                        ))?,
                        (None, _) => {
                            self.unexpected_eof_with_ctx("Expecting ';' ending a statement")?
                        }
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

    pub fn parse_trait_defn(&self) -> ParseResult<TraitDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_atom(TokenAtom::Keyword(Keyword::Trait)));

        let name = self.parse_ident()?;

        self.parse_token_atom(TokenAtom::Eq)?;
        let bound = self.parse_type_bound()?;

        // the next token should be a TokenTree delimited with a
        self.parse_arrow()?;

        let trait_type = self.parse_function_or_tuple_type(true)?;

        // @@Incomplete: we might want to have some kind of stacked errors to give more context rather
        //               than bubbling up from the simplest parsing functions to functions like these...
        // .ok_or_else(|| ParseError::Parsing {
        //     message: "Expected trait type here.".to_string(),
        //     src: self.source_location(&self.current_location()),
        // })?;

        Ok(TraitDef {
            name,
            bound,
            trait_type,
        })
    }

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
                self.next_token();
                let entries = self.parse_struct_def_entries()?;

                (None, entries)
            }
            _ => {
                return Err(ParseError::Parsing {
                    message: "Expected struct type args or struct definition entries here"
                        .to_string(),
                    src: self.source_location(&self.current_location()),
                })
            }
        };

        Ok(StructDef {
            name,
            bound,
            entries,
        })
    }

    pub fn parse_enum_defn(&self) -> ParseResult<EnumDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_atom(TokenAtom::Keyword(Keyword::Enum)));

        let name = self.parse_ident()?;

        self.parse_token_atom(TokenAtom::Eq)?;

        // now parse the optional type bound and the enum definition entries, if a type bound is
        // spe
        let (bound, entries) = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Lt) => {
                let bound = Some(self.parse_type_bound()?);
                self.parse_arrow()?;

                let entries = self.parse_enum_def_entries()?;

                (bound, entries)
            }

            Some(token) if token.is_brace_tree() => {
                self.next_token();
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
                self.next_token();

                let gen = self.from_stream(tree, *span);
                let mut entries = row![&self.wall;];
                while gen.has_token() {
                    let defn = gen.parse_enum_def_entry()?;
                    entries.push(defn, &self.wall);

                    if gen.has_token() {
                        gen.parse_token_atom(TokenAtom::Comma)?;
                    }
                }

                // Ensure the whole generator was exhausted
                if gen.has_token() {
                    gen.expected_eof()?;
                }

                Ok(entries)
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
            self.next_token();
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

    pub fn parse_struct_def_entries(&self) -> ParseResult<AstNodes<'c, StructDefEntry<'c>>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree),
                span,
            }) => {
                self.next_token();

                let gen = self.from_stream(tree, *span);
                let mut entries = row![&self.wall;];
                while gen.has_token() {
                    let defn = gen.parse_struct_def_entry()?;
                    entries.push(defn, &self.wall);

                    if gen.has_token() {
                        gen.parse_token_atom(TokenAtom::Comma)?;
                    }
                }

                // Ensure the whole generator was exhausted
                if gen.has_token() {
                    gen.expected_eof()?;
                }

                Ok(entries)
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

    pub fn parse_struct_def_entry(&self) -> ParseResult<AstNode<'c, StructDefEntry<'c>>> {
        let start = self.current_location();
        let name = self.parse_ident()?;

        let ty = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Colon) => {
                self.next_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        let default = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Eq) => {
                self.next_token();

                Some(self.parse_expression_bp(0)?)
            }
            _ => None,
        };

        Ok(self.node_from_joined_location(StructDefEntry { name, ty, default }, &start))
    }

    pub fn parse_type_bound(&self) -> ParseResult<AstNode<'c, Bound<'c>>> {
        let start = self.current_location();
        let type_args = self.parse_type_args()?;

        let trait_bounds = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Keyword(Keyword::Where)) => {
                self.next_token();

                let mut trait_bounds = row![&self.wall;];

                loop {
                    match self.peek() {
                        Some(Token {
                            kind: TokenKind::Atom(TokenAtom::Ident(ident)),
                            span: _,
                        }) => {
                            self.next_token();

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
                                    self.next_token();
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
        let iterator = self.parse_expression_bp(0)?;
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
        let condition = self.parse_expression_bp(0)?;
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

    pub fn parse_match_case(&self) -> ParseResult<AstNode<'c, MatchCase<'c>>> {
        let start = self.current_location();
        let pattern = self.parse_pattern()?;

        self.parse_arrow()?;
        let expr = self.parse_expression_bp(0)?;

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
        let subject = self.parse_expression_bp(0)?;
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
            self.disallow_struct_literals
                .set(self.lookahead_for_struct_literal());

            let clause = self.parse_expression_bp(0)?;
            let clause_loc = clause.location();

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
                    self.next_token();

                    match self.peek() {
                        Some(token) if token.has_atom(TokenAtom::Keyword(Keyword::If)) => {
                            // skip trying to convert just an 'else' branch since this is another if-branch
                            self.next_token();
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

    /// This is a utility function used to prevent struct literals from being
    /// parsed by some parsing function given that if there is an access name followed
    /// by two token trees that follow the access name.
    fn lookahead_for_struct_literal(&self) -> bool {
        // record the current location...
        let _start = self.current_location();

        // if self.peek_fn(self.parse_name_with_type_args(ident))
        false
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
                self.next_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        let value = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Eq) => {
                self.next_token();
                Some(self.parse_expression_bp(0)?)
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

    pub fn parse_pattern_collection(
        &self,
        tree: &Row<'c, Token<'c>>,
        span: Location,
    ) -> ParseResult<AstNodes<'c, Pattern<'c>>> {
        let gen = self.from_stream(tree, span);
        let mut elements = row![&self.wall;];

        while gen.has_token() {
            match gen.peek_resultant_fn(|| gen.parse_pattern()) {
                Some(pattern) => elements.push(pattern, &self.wall),
                None => break,
            }

            if gen.has_token() {
                gen.parse_token_atom(TokenAtom::Comma)?;
            }
        }

        if gen.has_token() {
            gen.expected_eof()?;
        }

        Ok(elements)
    }

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
                let copy = self.copy_name_node(&name);
                let loc = copy.location();
                self.node_with_location(Pattern::Binding(copy), loc)
            }
        };

        Ok(self.node_from_joined_location(DestructuringPattern { name, pattern }, &start))
    }

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
                self.next_token();

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
                            Pattern::Binding(self.make_name_from_id(k, span))
                        }
                    }
                }
            }
            token if token.kind.is_literal() => {
                self.next_token();
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
            //                 self.next_token();
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

    pub fn parse_block(&self) -> ParseResult<AstNode<'c, Block<'c>>> {
        let (gen, start) = match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree),
                span,
            }) => {
                self.next_token(); // step-along since we matched a block...

                (self.from_stream(tree, self.current_location()), *span)
            }
            Some(token) => {
                return Err(ParseError::Parsing {
                    message: format!(
                        "Expected block body, which begins with a '{{' but got a {}",
                        token
                    ),
                    src: self.source_location(&self.current_location()),
                });
            }
            // @@ErrorReporting
            None => self
                .error("Expected block body, which begins with a '{{', but reached end of input")?,
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

            // @@Incomplete: statements that begin with statement keywords shouldn't be bounded to having a semi-colon.
            if token.kind.begins_statement() {
                block.statements.push(gen.parse_statement()?, &self.wall);
                continue;
            }

            // if we can't tell if this is a statement, we parse an expression, and if there
            // is a following semi-colon, then we make this a statement and continue...
            let expr = gen.parse_expression_bp(0)?;
            let expr_loc = expr.location();

            match gen.peek() {
                Some(token) if token.has_atom(TokenAtom::Semi) => {
                    gen.next_token();

                    let expr_location = expr.location();
                    block.statements.push(
                        gen.node_with_location(Statement::Expr(expr), expr_location),
                        &self.wall,
                    );
                }
                Some(token) if token.has_atom(TokenAtom::Eq) && !gen.is_compound_expr.get() => {
                    gen.next_token();

                    // since this is followed by an expression, we try to parse another expression, and then
                    // ensure that after an expression there is a ending semi colon.
                    let rhs = gen.parse_expression_bp(0)?;

                    gen.parse_token_atom(TokenAtom::Semi)?;

                    block.statements.push(
                        gen.node_from_joined_location(
                            Statement::Assign(AssignStatement { lhs: expr, rhs }),
                            &expr_loc,
                        ),
                        &self.wall,
                    );
                }
                Some(token) => {
                    gen.unexpected_token_error(
                        &token.kind,
                        &TokenKindVector::from_row(row![&self.wall; TokenAtom::Semi]),
                        &gen.current_location(),
                    )?;
                }
                None => {
                    block.expr = Some(expr);
                    break;
                }
            };
        }

        Ok(self.node_from_joined_location(Block::Body(block), &start))
    }

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
                        // @@Hack: advance the token by one expecting it to be a tree, since parse block looks at the current
                        //         token instead of peeking ahead, this should be changed in the future.
                        self.next_token();

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
                if !is_func && self.peek_resultant_fn(|| self.parse_arrow()).is_some() {
                    self.offset.set(self.offset.get() - 2);
                    is_func = true;
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
                    self.next_token(); // eat the token since there isn't any alternative to being an ident or fn call.

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
                    self.next_token();
                    lhs_expr = self.parse_array_index(lhs_expr, tree, self.current_location())?;
                }
                // Function call
                TokenKind::Tree(Delimiter::Paren, tree) => {
                    self.next_token();
                    lhs_expr = self.parse_function_call(lhs_expr, tree, self.current_location())?;
                }
                // Struct literal
                TokenKind::Tree(Delimiter::Brace, tree) if !self.disallow_struct_literals.get() => {
                    self.next_token();
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

        gen.next_token(); // eat the string argument

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
            let arg = gen.parse_expression_bp(0);
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

    /// Function to parse the next token with the same kind as the specified kind, this
    /// is a useful utility function for parsing singular tokens in the place of more complex
    /// compound statements and expressions.
    pub fn parse_token_atom(&self, atom: TokenAtom) -> ParseResult<()> {
        match self.peek() {
            Some(token) if token.has_atom(atom) => {
                self.next_token();
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
            let value = gen.parse_expression_bp(0)?;

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

        Ok(AstNode::new(
            Expression::new(ExpressionKind::LiteralExpr(AstNode::new(
                Literal::Struct(StructLiteral {
                    name,
                    type_args,
                    entries,
                }),
                start.join(self.current_location()),
                &self.wall,
            ))),
            start.join(self.current_location()),
            &self.wall,
        ))
    }

    pub fn parse_array_index(
        &self,
        ident: AstNode<'c, Expression<'c>>,
        tree: &Row<'c, Token<'c>>,
        span: Location,
    ) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, span);
        let start = gen.current_location();

        // parse the indexing expression between the square brackets...
        let index_expr = gen.parse_expression_bp(0)?;
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
            TokenKind::Atom(TokenAtom::Amp) => ExpressionKind::Ref(self.parse_expression()?),
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

    pub fn parse_trait_bound(
        &self,
        ident: &Identifier,
    ) -> ParseResult<(AstNode<'c, AccessName<'c>>, AstNodes<'c, Type<'c>>)> {
        let name = self.parse_access_name(ident)?;

        let args = self.parse_type_args()?;

        Ok((name, args))
    }

    pub fn parse_name_with_type_args(
        &self,
        ident: &Identifier,
    ) -> ParseResult<(AstNode<'c, AccessName<'c>>, Option<AstNodes<'c, Type<'c>>>)> {
        let name = self.parse_access_name(ident)?;
        let args = self.peek_resultant_fn(|| self.parse_type_args());

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
                self.next_token();

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
                    self.next_token(); // :

                    match self.peek() {
                        Some(token) if token.has_atom(TokenAtom::Colon) => {
                            self.next_token(); // :

                            match self.peek() {
                                Some(Token {
                                    kind: TokenKind::Atom(TokenAtom::Ident(id)),
                                    span: _,
                                }) => {
                                    self.next_token();
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

    pub fn parse_expression_bp(
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
                None => break,
                Some(op) => {
                    // consume the number of tokens eaten whilst getting the operator...
                    (0..consumed_tokens).for_each(|_| {
                        self.next_token();
                    });

                    let op_span = op_start.join(self.current_location());

                    // check if we have higher precedence than the lhs expression...
                    let (l_prec, r_prec) = op.infix_binding_power();

                    if l_prec < min_prec {
                        self.offset.set(self.offset() - consumed_tokens as usize);
                        break;
                    }

                    // if the operator is a non-functional, (e.g. as) we need to perform a different conversion
                    // where we transform the AstNode into a different
                    if matches!(op, Operator::As) {
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
                        let rhs = self.parse_expression_bp(r_prec)?;
                        self.is_compound_expr.set(true);

                        // now convert the Operator into a function call...
                        lhs = self.node_from_joined_location(
                            Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                                subject: self.make_ident_from_op(op, &op_span),
                                args: self.node_from_joined_location(
                                    FunctionCallArgs {
                                        entries: row![&self.wall; lhs, rhs],
                                    },
                                    &op_span,
                                ),
                            })),
                            &op_start,
                        );
                    }
                }
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
                    self.next_token();
                }
                Some(token) if token.has_atom(TokenAtom::Gt) => {
                    self.next_token();
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

        // handle the function arguments first by checking for parentheses
        let mut type_args = match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(_, tree),
                span,
            }) => {
                self.next_token();

                let gen = self.from_stream(tree, *span);

                let mut type_args = row![&self.wall; ];

                // Handle special case where there is only one comma and no following items...
                // Special edge case for '(,)' or an empty tuple type...
                match gen.peek() {
                    Some(token) if token.has_atom(TokenAtom::Comma) => {
                        if gen.stream.len() == 1 {
                            gen.next_token();
                        }
                    }
                    _ => {
                        while gen.has_token() {
                            match gen.peek_resultant_fn(|| gen.parse_type()) {
                                Some(ty) => type_args.push(ty, &self.wall),
                                None => break,
                            };

                            // If we reach the end of the parenthesis don't try to parse the comma...
                            if gen.has_token() {
                                gen.parse_token_atom(TokenAtom::Comma)?;
                            }
                        }
                    }
                };

                type_args
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
                name: self.make_access_name(name, start.join(self.current_location())),
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
                self.next_token();

                // @@TODO: raw_refs...
                match self.parse_type() {
                    Ok(ty) => Type::Ref(ty),
                    err => return err,
                }
            }
            TokenKind::Atom(TokenAtom::Question) => {
                self.next_token();
                Type::Existential
            }
            TokenKind::Atom(TokenAtom::Ident(id)) => {
                self.next_token();

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
                self.next_token();

                let gen = self.from_stream(tree, token.span);

                let lhs_type = gen.parse_type()?;

                match gen.peek() {
                    // This must be a map
                    Some(token) if token.has_atom(TokenAtom::Colon) => {
                        gen.next_token();

                        let rhs_type = gen.parse_type()?;

                        // @@CopyPasta
                        if gen.has_token() {
                            gen.expected_eof()?;
                        }

                        // @@Incomplete: inline type names into ident map...
                        let name = IDENTIFIER_MAP.create_ident(MAP_TYPE_NAME);

                        Type::Named(NamedType {
                            name: self.make_access_name(name, token.span),
                            type_args: row![&self.wall; lhs_type, rhs_type],
                        })
                    }
                    Some(_) => gen.expected_eof()?,
                    None => {
                        // @@Incomplete: inline type names into ident map...
                        let name = IDENTIFIER_MAP.create_ident(SET_TYPE_NAME);

                        Type::Named(NamedType {
                            name: self.make_access_name(name, token.span),
                            type_args: row![&self.wall; lhs_type],
                        })
                    }
                }
            }

            // List type
            TokenKind::Tree(Delimiter::Bracket, tree) => {
                self.next_token();

                let gen = self.from_stream(tree, token.span);
                let inner_type = gen.parse_type()?;

                // @@CopyPasta
                if gen.has_token() {
                    gen.expected_eof()?;
                }

                // @@Incomplete: inline type names into ident map...
                let name = IDENTIFIER_MAP.create_ident(LIST_TYPE_NAME);

                Type::Named(NamedType {
                    name: self.make_access_name(name, token.span),
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
                    self.next_token();

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
                        let arg = gen.parse_expression_bp(0);
                        args.entries.push(arg?, &self.wall);

                        // now we eat the next token, checking that it is a comma
                        match gen.peek() {
                            Some(token) if token.has_atom(TokenAtom::Comma) => gen.next_token(),
                            _ => break,
                        };
                    }

                    Ok(self.node_with_location(
                        Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                            subject: self.make_ident_from_id(*id, *id_span),
                            args,
                        })),
                        start.join(self.current_location()),
                    ))
                }
                _ => Ok(self.make_ident_from_id(*id, *id_span)),
            },
            _ => Err(ParseError::Parsing {
                message: "Expecting field name after property access.".to_string(),
                src: self.source_location(&self.current_location()),
            }),
        }
    }

    pub fn empty_block(&self, span: &Location) -> AstNode<'c, Expression<'c>> {
        self.node_from_location(
            Expression::new(ExpressionKind::Block(self.node_from_location(
                Block::Body(BodyBlock {
                    statements: row![&self.wall],
                    expr: None,
                }),
                span,
            ))),
            span,
        )
    }

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
            return Ok(self.empty_block(span));
        }

        // Here we have to parse the initial expression and then check if there is a specific
        // separator. We have to check:
        //
        // - If an expression is followed by a comma separator, it must be a set literal.
        //
        // - If an expression is followed by a ':' (colon), it must be a map literal.
        //
        // - Otherwise, it must be a block and we should continue parsing the block from here
        let initial_expr = gen.parse_expression_bp(0)?;

        match gen.peek() {
            Some(token) if token.has_atom(TokenAtom::Comma) => {
                gen.next_token(); // ','

                let literal = self.parse_set_literal(gen, initial_expr)?;

                Ok(self.node_from_location(
                    Expression::new(ExpressionKind::LiteralExpr(literal)),
                    span,
                ))
            }
            Some(token) if token.has_atom(TokenAtom::Colon) => {
                gen.next_token(); // ':'

                let start_pos = initial_expr.location();
                let entry = self.node_from_joined_location(
                    MapLiteralEntry {
                        key: initial_expr,
                        value: gen.parse_expression_bp(0)?,
                    },
                    &start_pos,
                );

                // Peek ahead to check if there is a comma, if there is then we'll parse more map entries,
                // and pass it into parse_map_literal.
                match gen.peek() {
                    Some(token) if token.has_atom(TokenAtom::Comma) => {
                        gen.next_token();

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
            Some(_) => {
                gen.parse_token_atom(TokenAtom::Semi)?;

                let statement_loc = initial_expr.location().join(gen.current_location());
                let statement =
                    self.node_with_location(Statement::Expr(initial_expr), statement_loc);

                // check here if there is a 'semi', and then convert the expression into a statement.
                let block = self.parse_block_from_gen(&gen, *span, Some(statement))?;

                Ok(self.node_from_location(Expression::new(ExpressionKind::Block(block)), span))
            }
            None => {
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
        }
    }

    pub fn parse_map_entry(&self) -> ParseResult<AstNode<'c, MapLiteralEntry<'c>>> {
        let start = self.current_location();

        let key = self.parse_expression_bp(0)?;
        self.parse_token_atom(TokenAtom::Colon)?;
        let value = self.parse_expression_bp(0)?;

        Ok(self.node_from_joined_location(MapLiteralEntry { key, value }, &start))
    }

    pub fn parse_map_literal(
        &self,
        gen: Self,
        initial_entry: AstNode<'c, MapLiteralEntry<'c>>,
    ) -> ParseResult<AstNode<'c, Literal<'c>>> {
        let start = gen.current_location();
        let mut elements = row![&self.wall; initial_entry];

        // so parse the arguments to the function here... with potential type annotations
        while gen.has_token() {
            match gen.peek_resultant_fn(|| gen.parse_map_entry()) {
                Some(element) => elements.push(element, &self.wall),
                None => break,
            }

            if gen.has_token() {
                gen.parse_token_atom(TokenAtom::Comma)?;
            }
        }

        if gen.has_token() {
            gen.expected_eof()?;
        }

        Ok(self.node_from_joined_location(Literal::Map(MapLiteral { elements }), &start))
    }

    pub fn parse_set_literal(
        &self,
        gen: Self,
        initial_entry: AstNode<'c, Expression<'c>>,
    ) -> ParseResult<AstNode<'c, Literal<'c>>> {
        let start = self.current_location();

        let mut elements = row![&self.wall; initial_entry];

        // so parse the arguments to the function here... with potential type annotations
        while gen.has_token() {
            match gen.peek_resultant_fn(|| gen.parse_expression_bp(0)) {
                Some(element) => elements.push(element, &self.wall),
                None => break,
            }

            if gen.has_token() {
                gen.parse_token_atom(TokenAtom::Comma)?;
            }
        }

        if gen.has_token() {
            gen.expected_eof()?;
        }

        Ok(self.node_from_joined_location(Literal::Set(SetLiteral { elements }), &start))
    }

    pub fn parse_pattern_with_if(&self) -> ParseResult<AstNode<'c, Pattern<'c>>> {
        let start = self.current_location();
        let pattern = self.parse_singular_pattern()?;

        match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Keyword(Keyword::If)) => {
                self.next_token();

                let condition = self.parse_expression_bp(0)?;

                Ok(self.node_from_joined_location(
                    Pattern::If(IfPattern { pattern, condition }),
                    &start,
                ))
            }
            _ => Ok(pattern),
        }
    }

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
                    self.next_token();
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

    pub fn parse_function_def_arg(&self) -> ParseResult<AstNode<'c, FunctionDefArg<'c>>> {
        let start = self.current_location();
        let name = self.parse_ident()?;

        let ty = match self.peek() {
            Some(token) if token.has_atom(TokenAtom::Colon) => {
                self.next_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        Ok(self.node_from_joined_location(FunctionDefArg { name, ty }, &start))
    }

    pub fn parse_function_literal(&self, gen: &Self) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let start = self.current_location();

        let mut args = row![&self.wall;];

        // so parse the arguments to the function here... with potential type annotations
        while gen.has_token() {
            match gen.peek_resultant_fn(|| gen.parse_function_def_arg()) {
                Some(arg) => args.push(arg, &self.wall),
                None => break,
            }

            if gen.has_token() {
                gen.parse_token_atom(TokenAtom::Comma)?;
            }
        }

        if gen.has_token() {
            gen.expected_eof()?;
        }

        // check if there is a return type
        let return_ty = match self.peek_resultant_fn(|| self.parse_token_atom(TokenAtom::Colon)) {
            Some(_) => Some(self.parse_type()?),
            _ => None,
        };

        self.parse_arrow()?;

        let fn_body = match self.peek() {
            Some(_) => self.parse_expression_bp(0)?,
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
                    gen.next_token();

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

        let expr = gen.parse_expression_bp(0)?;

        // Check if this is just a singularly wrapped expression
        if gen.peek().is_none() {
            return Ok(expr);
        }

        let mut elements = row![&self.wall; expr];

        loop {
            match gen.peek() {
                Some(token) if token.has_atom(TokenAtom::Comma) => {
                    gen.next_token();

                    // Handles the case where this is a trailing comma and no tokens after...
                    if !gen.has_token() {
                        break;
                    }

                    elements.push(gen.parse_expression_bp(0)?, &self.wall)
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

    pub fn parse_array_literal(
        &self,
        tree: &Row<'c, Token<'c>>,
        span: &Location,
    ) -> ParseResult<AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, *span);
        let start = gen.current_location();

        let mut elements = row![&self.wall];

        while gen.has_token() {
            let expr = gen.parse_expression_bp(0)?;
            elements.push(expr, &self.wall);

            match gen.peek() {
                Some(token) if token.has_atom(TokenAtom::Comma) => {
                    gen.next_token();
                }
                Some(token) => {
                    // if we haven't exhausted the whole token stream, then report this as a unexpected
                    // token error
                    return Err(ParseError::Parsing {
                        message: format!(
                            "Unexpected token '{}' in the place of an comma.",
                            token.kind
                        ),
                        src: gen.source_location(&gen.current_location()),
                    });
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
