//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use std::{cell::Cell, iter, vec};

use hash_ast::{
    ast::*,
    error::{ParseError, ParseResult},
    ident::{Identifier, IDENTIFIER_MAP},
    keyword::Keyword,
    location::{Location, SourceLocation},
    module::ModuleIdx,
    resolve::ModuleResolver,
};
use smallvec::smallvec;

use crate::{
    operator::Operator,
    token::{Delimiter, Token, TokenKind, TokenKindVector},
};

pub struct AstGen<'a, R> {
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
    stream: Vec<Token>,

    /// State set by expression parsers for parents to let them know if the parsed expression
    /// was made up of multiple expressions with precedence operators.
    is_compound_expr: Cell<bool>,

    /// State to prevent from struct literals being parsed in the current expression, because
    /// the parent has specifically checked ahead to ensure it isn't a struct literal.
    disallow_struct_literals: Cell<bool>,

    /// Instance of a [ModuleResolver] to notify the parser of encountered imports.
    resolver: &'a R,
}

/// Implementation of the [AstGen] with accompanying functions to parse specific
/// language components.
impl<'a, R> AstGen<'a, R>
where
    R: ModuleResolver,
{
    pub fn new(stream: Vec<Token>, resolver: &'a R) -> Self {
        Self {
            stream,
            parent_span: None,
            is_compound_expr: Cell::new(false),
            disallow_struct_literals: Cell::new(false),
            offset: Cell::new(0),
            resolver,
        }
    }

    pub fn from_stream(&self, stream: Vec<Token>, parent_span: Location) -> Self {
        Self {
            stream,
            offset: Cell::new(0),
            is_compound_expr: Cell::new(false),
            disallow_struct_literals: Cell::new(false),
            parent_span: Some(parent_span),
            resolver: self.resolver,
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
    pub(crate) fn peek_nth(&self, at: usize) -> Option<&Token> {
        self.stream.get(self.offset.get() + at)
    }

    pub(crate) fn peek(&self) -> Option<&Token> {
        self.peek_nth(0)
    }

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

    /// Function that increases the offset of the next token
    pub(crate) fn next_token(&self) -> Option<&Token> {
        let value = self.stream.get(self.offset.get());

        if value.is_some() {
            // @@Dumbness: because Cell::update is unsafe
            self.offset.set(self.offset.get() + 1);
        }

        value
    }

    pub(crate) fn current_token(&self) -> &Token {
        self.stream.get(self.offset.get() - 1).unwrap()
    }

    /// Get the current location from the current token, if there is no token at the current
    /// offset, then the location of the last token is used,
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
    pub fn node<T>(&self, inner: T) -> AstNode<T> {
        AstNode::new(inner, self.current_location())
    }

    /// Create a new [AstNode] from the information provided by the [AstGen]
    pub fn node_with_location<T>(&self, inner: T, location: Location) -> AstNode<T> {
        AstNode::new(inner, location)
    }

    fn copy_name_node(&self, name: &AstNode<Name>) -> AstNode<Name> {
        self.node(Name { ..*name.body() })
    }

    pub(crate) fn unexpected_token_error(
        &self,
        kind: &TokenKind,
        expected: &TokenKindVector,
        location: &Location,
    ) -> ParseError {
        ParseError::Parsing {
            message: format!("Unexpected token '{}', expecting {}", kind, expected),
            src: self.source_location(location),
        }
    }

    pub(crate) fn make_ident(&self, name: AstString, location: &Location) -> AstNode<Expression> {
        AstNode::new(
            Expression::new(ExpressionKind::Variable(VariableExpr {
                name: self.node_from_joined_location(
                    AccessName {
                        path: smallvec![IDENTIFIER_MAP.create_ident(name)],
                    },
                    location,
                ),
                type_args: vec![],
            })),
            *location,
        )
    }

    pub(crate) fn make_ident_from_id(
        &self,
        id: &Identifier,
        location: Location,
    ) -> AstNode<Expression> {
        AstNode::new(
            Expression::new(ExpressionKind::Variable(VariableExpr {
                name: self.node_from_joined_location(
                    AccessName {
                        path: smallvec![*id],
                    },
                    &location,
                ),
                type_args: vec![],
            })),
            location,
        )
    }

    pub(crate) fn make_ident_from_op(
        &self,
        op: Operator,
        location: &Location,
    ) -> AstNode<Expression> {
        self.make_ident(AstString::Owned(op.as_str().to_owned()), location)
    }

    pub(crate) fn node_from_location<T>(&self, body: T, location: &Location) -> AstNode<T> {
        AstNode::new(body, *location)
    }

    pub(crate) fn node_from_joined_location<T>(&self, body: T, start: &Location) -> AstNode<T> {
        AstNode::new(body, start.join(self.current_location()))
    }

    /// Function to peek ahead and match some parsing function that returns a [Option<T>] wrapped
    /// in a [ParseResult]. If The result is an error, or the option is [None], the function will
    /// reset the current offset of the token stream to where it was the function was peeked.
    pub fn peek_fn<T>(
        &self,
        parse_fn: impl Fn() -> ParseResult<Option<T>>,
    ) -> ParseResult<Option<T>> {
        let start = self.offset.get();

        match parse_fn() {
            result @ Ok(Some(_)) => result,
            err => {
                self.offset.set(start);
                err
            }
        }
    }

    /// Parse a [Module] which is simply made of a list of statements
    pub fn parse_module(&self) -> ParseResult<Module> {
        let mut contents = vec![];

        while self.has_token() {
            contents.push(self.parse_statement()?);
        }

        Ok(Module { contents })
    }

    pub fn parse_statement(&self) -> ParseResult<AstNode<Statement>> {
        let start = self.current_location();

        match self.peek() {
            Some(Token {
                kind: TokenKind::Keyword(kw),
                span: _,
            }) => {
                self.next_token();

                let statement =
                    match kw {
                        Keyword::Let => Statement::Let(self.parse_let_statement()?),
                        Keyword::For => Statement::Block(self.parse_for_loop()?),
                        Keyword::While => Statement::Block(self.parse_while_loop()?),
                        Keyword::Loop => {
                            // @@Hack: advance the token by one expecting it to be a tree, since parse block looks at the current
                            //         token instead of peeking ahead, this should be changed in the future.
                            self.next_token();

                            Statement::Block(self.node_from_joined_location(
                                Block::Loop(self.parse_block()?),
                                &start,
                            ))
                        }
                        Keyword::If => Statement::Block(self.parse_if_statement()?),
                        Keyword::Match => Statement::Block(self.parse_match_block()?),
                        Keyword::Trait => Statement::TraitDef(self.parse_trait_defn()?),
                        Keyword::Enum => Statement::EnumDef(self.parse_enum_defn()?),
                        Keyword::Struct => Statement::StructDef(self.parse_struct_defn()?),
                        Keyword::Continue => Statement::Continue,
                        Keyword::Break => Statement::Break,
                        Keyword::Return => {
                            // @@Hack: check if the next token is a semi-colon, if so the return statement
                            // has no returned expression...
                            match self.peek() {
                                Some(token) if token.has_kind(TokenKind::Semi) => {
                                    Statement::Return(None)
                                }
                                Some(_) => Statement::Return(Some(self.parse_expression_bp(0)?)),
                                None => Statement::Return(None),
                            }
                        }
                        kw => {
                            return Err(ParseError::Parsing {
                                message: format!(
                                    "Unexpected keyword '{}' at the beginning of a statement",
                                    kw
                                ),
                                src: self.source_location(&self.current_location()),
                            })
                        }
                    };

                match self.next_token() {
                    Some(token) if token.has_kind(TokenKind::Semi) => {
                        Ok(AstNode::new(statement, start.join(self.current_location())))
                    }
                    Some(token) => Err(ParseError::Parsing {
                        message: format!(
                            "Expecting ';' at the end of a statement, but got '{}' ",
                            token.kind
                        ),
                        src: self.source_location(&self.current_location()),
                    }),
                    None => Err(ParseError::Parsing {
                        message: "Expecting ';' ending a statement, but reached the end of file."
                            .to_string(),
                        src: self.source_location(&self.current_location()),
                    }),
                }
            }
            Some(_) => {
                let expr = self.parse_expression_bp(0)?;

                // Ensure that the next token is a Semi
                match self.next_token() {
                    Some(token) if token.has_kind(TokenKind::Semi) => Ok(AstNode::new(
                        Statement::Expr(expr),
                        start.join(self.current_location()),
                    )),
                    Some(token) => Err(ParseError::Parsing {
                        message: format!(
                            "Expecting ';' at the end of a statement, but got '{}' ",
                            token.kind
                        ),
                        src: self.source_location(&self.current_location()),
                    }),
                    None => Err(ParseError::Parsing {
                        message: "Expecting ';' ending a statement, but reached the end of file."
                            .to_string(),
                        src: self.source_location(&self.current_location()),
                    }),
                }
            }
            _ => Err(ParseError::Parsing {
                message: "Expected statement".to_string(),
                src: self.source_location(&self.current_location()),
            }),
        }
    }

    /// This function is used to exclusively parse a interactive block which follows
    /// similar rules to a an actual block. Interactive statements are like ghost blocks
    /// without the actual braces to begin with. It follows that there are an arbitrary
    /// number of statements, followed by an optional final expression which doesn't
    /// need to be completed by a comma...
    pub fn parse_expression_from_interactive(&self) -> ParseResult<AstNode<BodyBlock>> {
        // get the starting position
        let start = self.current_location();

        let mut block = BodyBlock {
            statements: vec![],
            expr: None,
        };

        // Just return an empty block if we don't get anything
        if self.stream.is_empty() {
            return Ok(self.node_with_location(block, start));
        }

        // firstly check if the first token signals a beginning of a statement, we can tell
        // this by checking for keywords that must begin a statement...
        while self.has_token() {
            let token = self.peek().unwrap();

            if token.kind.begins_statement() {
                block.statements.push(self.parse_statement()?);
                continue;
            }

            // if we can't tell if this is a statement, we parse an expression, and if there
            // is a following semi-colon, then we make this a statement and continue...
            let expr = self.parse_expression_bp(0)?;
            let expr_loc = expr.location();

            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Semi) => {
                    self.next_token();

                    let expr_location = expr.location();
                    block
                        .statements
                        .push(self.node_with_location(Statement::Expr(expr), expr_location));
                }
                Some(token) if token.has_kind(TokenKind::Eq) && !self.is_compound_expr.get() => {
                    self.next_token();

                    // since this is followed by an expression, we try to parse another expression, and then
                    // ensure that after an expression there is a ending semi colon.
                    let rhs = self.parse_expression_bp(0)?;

                    self.parse_token_kind(TokenKind::Semi)?;

                    block.statements.push(self.node_from_joined_location(
                        Statement::Assign(AssignStatement { lhs: expr, rhs }),
                        &expr_loc,
                    ));
                }
                Some(token) => {
                    return Err(self.unexpected_token_error(
                        &token.kind,
                        &TokenKindVector::from_slice(&[TokenKind::Semi]),
                        &self.current_location(),
                    ))
                }
                None => {
                    block.expr = Some(expr);
                    break;
                }
            };
        }

        Ok(self.node_with_location(block, start.join(self.current_location())))
    }

    pub fn parse_trait_defn(&self) -> ParseResult<TraitDef> {
        todo!()
    }

    pub fn parse_struct_defn(&self) -> ParseResult<StructDef> {
        todo!()
    }

    pub fn parse_enum_defn(&self) -> ParseResult<EnumDef> {
        todo!()
    }

    pub fn parse_type_bound(&self) -> ParseResult<AstNode<Bound>> {
        todo!()
    }

    pub fn parse_for_loop(&self) -> ParseResult<AstNode<Block>> {
        todo!()
    }

    pub fn parse_while_loop(&self) -> ParseResult<AstNode<Block>> {
        todo!()
    }

    pub fn parse_match_block(&self) -> ParseResult<AstNode<Block>> {
        todo!()
    }

    // we transpile if-else blocks into match blocks in order to simplify
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
    pub fn parse_if_statement(&self) -> ParseResult<AstNode<Block>> {
        debug_assert!(matches!(
            self.current_token().kind,
            TokenKind::Keyword(Keyword::If)
        ));

        let start = self.current_location();

        let mut cases = vec![];
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

            cases.push(self.node_from_location(
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
            ));

            // Now check if there is another branch after the else or if, and loop onwards...
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Else)) => {
                    self.next_token();

                    match self.peek() {
                        Some(token) if token.has_kind(TokenKind::Keyword(Keyword::If)) => {
                            // skip trying to convert just an 'else' branch since this is another if-branch
                            self.next_token();
                            continue;
                        }
                        _ => (),
                    };

                    // this is the final branch of the if statement, and it is added to the end
                    // of the statements...
                    self.next_token();
                    let start = self.current_location();

                    let else_branch = self.parse_block()?;
                    let loc = start.join(else_branch.location());

                    has_else_branch = true;

                    cases.push(self.node_from_location(
                        MatchCase {
                            pattern: self.node(Pattern::Ignore),
                            expr: self.node_from_location(
                                Expression::new(ExpressionKind::Block(else_branch)),
                                &loc,
                            ),
                        },
                        &loc,
                    ));

                    break;
                }
                _ => break,
            };
        }

        if !has_else_branch {
            cases.push(self.node(MatchCase {
                pattern: self.node(Pattern::Ignore),
                expr: self.node(Expression::new(ExpressionKind::Block(self.node(
                    Block::Body(BodyBlock {
                        statements: vec![],
                        expr: None,
                    }),
                )))),
            }));
        }

        Ok(self.node_from_joined_location(
            Block::Match(MatchBlock {
                subject: self.make_ident(AstString::Borrowed("true"), &self.current_location()),
                cases,
            }),
            &start,
        ))
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

    pub fn parse_let_statement(&self) -> ParseResult<LetStatement> {
        todo!()
    }

    /// Function to parse a block body
    pub fn parse_block(&self) -> ParseResult<AstNode<Block>> {
        let (gen, start) = match self.current_token() {
            Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree),
                span,
            } => (
                self.from_stream(tree.to_owned(), self.current_location()),
                *span,
            ),
            token => {
                return Err(ParseError::Parsing {
                    message: format!(
                        "Expected block body, which begins with a '{{' but got a {}",
                        token
                    ),
                    src: self.source_location(&self.current_location()),
                });
            }
        };

        let mut block = BodyBlock {
            statements: vec![],
            expr: None,
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
                block.statements.push(gen.parse_statement()?);
                continue;
            }

            // if we can't tell if this is a statement, we parse an expression, and if there
            // is a following semi-colon, then we make this a statement and continue...
            let expr = gen.parse_expression_bp(0)?;
            let expr_loc = expr.location();

            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Semi) => {
                    gen.next_token();

                    let expr_location = expr.location();
                    block
                        .statements
                        .push(gen.node_with_location(Statement::Expr(expr), expr_location));
                }
                Some(token) if token.has_kind(TokenKind::Eq) && !gen.is_compound_expr.get() => {
                    gen.next_token();

                    // since this is followed by an expression, we try to parse another expression, and then
                    // ensure that after an expression there is a ending semi colon.
                    let rhs = gen.parse_expression_bp(0)?;

                    gen.parse_token_kind(TokenKind::Semi)?;

                    block.statements.push(gen.node_from_joined_location(
                        Statement::Assign(AssignStatement { lhs: expr, rhs }),
                        &expr_loc,
                    ));
                }
                Some(token) => {
                    return Err(gen.unexpected_token_error(
                        &token.kind,
                        &TokenKindVector::from_slice(&[TokenKind::Semi]),
                        &gen.current_location(),
                    ))
                }
                None => {
                    block.expr = Some(expr);
                    break;
                }
            };
        }

        Ok(self.node_from_joined_location(Block::Body(block), &start))
    }

    pub fn parse_expression(&self) -> ParseResult<AstNode<Expression>> {
        let token = self.next_token();

        if token.is_none() {
            return Err(ParseError::Parsing {
                message: "Expected the beginning of an expression here.".to_string(),
                src: SourceLocation {
                    location: self.current_location(),
                    module_index: ModuleIdx(0),
                },
            });
        }

        let token = token.unwrap();

        // ::CompoundExpressions: firstly, we have to get the initial part of the expression, and then we can check
        // if there are any additional parts in the forms of either property accesses, indexing or infix function calls
        let subject = match &token.kind {
            kind if kind.is_unary_op() => return self.parse_unary_expression(),

            // Handle primitive literals
            kind if kind.is_literal() => self.parse_literal(),
            TokenKind::Ident(_) => {
                // record the starting span
                let start = self.current_location();

                // extract the identifier value and span from the current token
                let ident = match self.current_token() {
                    Token {
                        kind: TokenKind::Ident(id),
                        span: _,
                    } => id,
                    _ => unreachable!(),
                };

                let (name, type_args) = self.parse_name_with_type_args(ident)?;
                let type_args = type_args.unwrap_or_default();

                // create the lhs expr.
                self.node_with_location(
                    Expression::new(ExpressionKind::Variable(VariableExpr { name, type_args })),
                    start.join(self.current_location()),
                )
            }

            // Handle tree literals
            TokenKind::Tree(Delimiter::Brace, tree) => {
                self.parse_block_or_braced_literal(tree, &self.current_location())?
            }
            TokenKind::Tree(Delimiter::Bracket, tree) => {
                self.parse_array_literal(tree, &self.current_location())?
            } // Could be an array index?
            TokenKind::Tree(Delimiter::Paren, tree) => {
                self.disallow_struct_literals.set(true); // @@Cleanup
                self.parse_expression_or_tuple(tree, &self.current_location())?
            }

            TokenKind::Keyword(kw) => {
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
        subject: AstNode<Expression>,
    ) -> ParseResult<AstNode<Expression>> {
        // record the starting span
        let start = self.current_location();

        let mut lhs_expr = subject;

        // so here we need to peek to see if this is either a index_access, field access or a function call...
        while let Some(next_token) = self.peek() {
            match &next_token.kind {
                // Property access or infix function call
                TokenKind::Dot => {
                    self.next_token(); // eat the token since there isn't any alternative to being an ident or fn call.

                    let name_or_fn_call = self.parse_name_or_infix_call()?;
                    let kind = name_or_fn_call.into_body().into_kind();

                    match kind {
                        ExpressionKind::FunctionCall(FunctionCallExpr { subject, mut args }) => {
                            // @@Future: @@FunctionArguments:
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
                            args.entries.insert(0, lhs_expr);

                            lhs_expr = AstNode::new(
                                Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                                    subject,
                                    args,
                                })),
                                start.join(self.current_location()),
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
                    lhs_expr = self.parse_array_index(&lhs_expr, tree, &self.current_location())?;
                }
                // Function call
                TokenKind::Tree(Delimiter::Paren, tree) => {
                    self.next_token();
                    lhs_expr =
                        self.parse_function_call(lhs_expr, tree, &self.current_location())?;
                }
                // Struct literal
                TokenKind::Tree(Delimiter::Brace, tree) if !self.disallow_struct_literals.get() => {
                    self.next_token();
                    // Ensure that the LHS of the brace is a variable, since struct literals can only
                    // be begun with variable names and type arguments, any other expression cannot be
                    // the beginning of a struct literal.
                    match lhs_expr.kind() {
                        ExpressionKind::Variable(VariableExpr { name, type_args }) => {
                            lhs_expr = self.parse_struct_literal(name, type_args, tree)?;
                        }
                        _ => break, // _ => return Err(ParseError::Parsing {
                                    //     message: "Unexpected beginning of a block, if this is a struct literal, it should begin with a variable name.".to_string(),
                                    //     src: self.source_location(&self.current_location()),
                                    // })
                    };
                }
                _ => break,
            }
        }

        // reset disallowing struct literals
        self.disallow_struct_literals.set(false);

        Ok(lhs_expr)
    }

    pub fn parse_function_call(
        &self,
        ident: AstNode<Expression>,
        tree: &[Token],
        span: &Location,
    ) -> ParseResult<AstNode<Expression>> {
        let gen = self.from_stream(tree.to_owned(), *span);
        let mut args = AstNode::new(FunctionCallArgs { entries: vec![] }, *span);

        while gen.has_token() {
            let arg = gen.parse_expression_bp(0);
            args.entries.push(arg?);

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

    /// Function to parse the next token with the same kind as the specified kind, this
    /// is a useful utility function for parsing singular tokens in the place of more complex
    /// compound statements and expressions.
    pub fn parse_token_kind(&self, kind: TokenKind) -> ParseResult<()> {
        match self.peek() {
            Some(token) if token.has_kind(kind.clone()) => {
                self.next_token();
                Ok(())
            }
            Some(token) => Err(ParseError::Parsing {
                message: format!("Expected a '{}', but got a '{}'", kind, token.kind),
                src: self.source_location(&token.span),
            }),
            _ => Err(ParseError::Parsing {
                message: "Unexpected end of input".to_string(),
                src: self.source_location(&self.current_location()),
            }),
        }
    }

    pub fn parse_struct_literal(
        &self,
        name: &AstNode<AccessName>,
        type_args: &[AstNode<Type>],
        tree: &[Token],
    ) -> ParseResult<AstNode<Expression>> {
        let start = self.current_location();
        let gen = self.from_stream(tree.to_owned(), start);

        let mut entries = vec![];

        while gen.has_token() {
            let entry_start = gen.current_location();

            let name = gen.parse_ident()?;
            gen.parse_token_kind(TokenKind::Eq)?;
            let value = gen.parse_expression_bp(0)?;

            entries.push(gen.node_with_location(
                StructLiteralEntry { name, value },
                entry_start.join(gen.current_location()),
            ));

            // now we eat the next token, checking that it is a comma
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => gen.next_token(),
                _ => break,
            };
        }

        Ok(AstNode::new(
            Expression::new(ExpressionKind::LiteralExpr(AstNode::new(
                Literal::Struct(StructLiteral {
                    // @@RedundantCopying @@RedundantCopying @@RedundantCopying
                    name: name.to_owned(),
                    type_args: type_args.to_vec(),
                    entries,
                }),
                start.join(self.current_location()),
            ))),
            start.join(self.current_location()),
        ))
    }

    pub fn parse_array_index(
        &self,
        ident: &AstNode<Expression>,
        tree: &[Token],
        span: &Location,
    ) -> ParseResult<AstNode<Expression>> {
        let gen = self.from_stream(tree.to_vec(), *span);
        let start = gen.current_location();

        // parse the indexing expression between the square brackets...
        let index_expr = gen.parse_expression_bp(0)?;
        let index_loc = index_expr.location();

        // since nothing should be after the expression, we can check that no tokens
        // are left and the generator is empty, otherwise report this as an unexpected_token
        if gen.has_token() {
            let token = gen.next_token().unwrap();
            return Err(self.unexpected_token_error(
                &token.kind,
                &TokenKindVector::empty(),
                &gen.current_location(),
            ));
        }

        Ok(self.node_with_location(
            Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                subject: self.make_ident(AstString::Borrowed("index"), &start),
                args: self.node_with_location(
                    FunctionCallArgs {
                        entries: vec![ident.to_owned(), index_expr],
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
    pub fn parse_unary_expression(&self) -> ParseResult<AstNode<Expression>> {
        let token = self.current_token();
        let start = self.current_location();

        let expr_kind = match &token.kind {
            TokenKind::Star => ExpressionKind::Deref(self.parse_expression()?),
            TokenKind::Amp => ExpressionKind::Ref(self.parse_expression()?),
            kind @ (TokenKind::Plus | TokenKind::Minus) => {
                let expr = self.parse_expression()?;
                let loc = expr.location();

                let fn_name = match kind {
                    TokenKind::Plus => "pos",
                    TokenKind::Minus => "neg",
                    _ => unreachable!(),
                };

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident(AstString::Borrowed(fn_name), &start),
                    args: self.node_from_location(
                        FunctionCallArgs {
                            entries: vec![expr],
                        },
                        &loc,
                    ),
                })
            }
            TokenKind::Tilde => {
                let arg = self.parse_expression()?;
                let loc = arg.location();

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident(AstString::Borrowed("notb"), &start),
                    args: self.node_from_location(FunctionCallArgs { entries: vec![arg] }, &loc),
                })
            }
            TokenKind::Exclamation => {
                let arg = self.parse_expression()?;
                let loc = arg.location();

                ExpressionKind::FunctionCall(FunctionCallExpr {
                    subject: self.make_ident(AstString::Borrowed("not"), &start),
                    args: self.node_from_location(FunctionCallArgs { entries: vec![arg] }, &loc),
                })
            }
            kind => panic!("Expected token to be a unary operator, but got '{}'", kind),
        };

        Ok(self.node_from_joined_location(Expression::new(expr_kind), &start))
    }

    pub fn parse_name_with_type_args(
        &self,
        ident: &Identifier,
    ) -> ParseResult<(AstNode<AccessName>, Option<AstNodes<Type>>)> {
        let name = self.parse_access_name(ident)?;
        let args = self.peek_fn(|| self.parse_type_args())?;

        Ok((name, args))
    }

    /// Parses a single identifier, essentially converting the current [TokenKind::Ident] into
    /// an [AstNode<Name>], assuming that the next token is an identifier.
    pub fn parse_ident(&self) -> ParseResult<AstNode<Name>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Ident(ident),
                span,
            }) => {
                self.next_token();

                Ok(AstNode::new(Name { ident: *ident }, *span))
            }
            _ => Err(ParseError::Parsing {
                message: "Expected an identifier".to_string(),
                src: self.source_location(&self.current_location()),
            }),
        }
    }

    /// Parse an [AccessName] from the current token stream. An [AccessName] is defined as
    /// a number of identifiers that are separated by the namespace operator '::'. The function
    /// presumes that the current token is an identifier an that the next token is a colon.
    pub fn parse_access_name(&self, start_id: &Identifier) -> ParseResult<AstNode<AccessName>> {
        let start = self.current_location();
        let mut path = smallvec![*start_id];

        loop {
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Colon) => {
                    self.next_token();

                    let second_colon = self.peek();

                    // Ensure the second colon is present...
                    if second_colon.is_none() || !second_colon.unwrap().has_kind(TokenKind::Colon) {
                        return Err(ParseError::Parsing {
                            message: "Expected ':' after the beginning of an namespace".to_string(),
                            src: self.source_location(&self.current_location()),
                        });
                    }

                    self.next_token();

                    match self.peek() {
                        Some(Token {
                            kind: TokenKind::Ident(id),
                            span: _,
                        }) => {
                            self.next_token();
                            path.push(*id);
                        }
                        _ => {
                            return Err(ParseError::Parsing {
                                message: "Expected identifier after a name access".to_string(),
                                src: self.source_location(&self.current_location()),
                            })
                        }
                    }
                }
                _ => break,
            }
        }

        Ok(AstNode::new(
            AccessName { path },
            start.join(self.current_location()),
        ))
    }

    /// Special variant of expression to handle interactive statements that have relaxed rules about
    /// semi-colons for some statements.
    pub fn parse_expression_bp(&self, min_prec: u8) -> ParseResult<AstNode<Expression>> {
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
                        break;
                    }

                    let rhs = self.parse_expression_bp(r_prec)?;
                    self.is_compound_expr.set(true);

                    // now convert the Operator into a function call...
                    lhs = AstNode::new(
                        Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                            subject: self.make_ident_from_op(op, &op_span),
                            args: self.node_from_joined_location(
                                FunctionCallArgs {
                                    entries: vec![lhs, rhs],
                                },
                                &op_span,
                            ),
                        })),
                        op_span,
                    )
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
    pub fn parse_type_args(&self) -> ParseResult<Option<AstNodes<Type>>> {
        // Ensure this is the beginning of a type_bound
        if self.peek().is_none() || !self.peek().unwrap().has_kind(TokenKind::Lt) {
            return Ok(None);
        }

        self.next_token();

        let mut type_args = vec![];
        let mut has_comma = false;

        loop {
            // Check if the type argument is parsed, if we have already encountered a comma, we
            // return a hard error because it has already started on a comma.
            match self.parse_type()? {
                Some(ty) => type_args.push(ty),
                _ if has_comma => {
                    return Err(ParseError::Parsing {
                        message: "Expected type argument in a type bound.".to_string(),
                        src: self.source_location(&self.current_location()),
                    })
                }
                _ => return Ok(None),
            };

            // Now consider if the bound is closing or continuing with a comma...
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    self.next_token();
                    has_comma = true;
                }
                Some(token) if token.has_kind(TokenKind::Gt) => {
                    self.next_token();
                    break;
                }
                _ => return Ok(None),
            }
        }

        Ok(Some(type_args))
    }

    /// Function to parse a type
    pub fn parse_type(&self) -> ParseResult<Option<AstNode<Type>>> {
        let start = self.current_location();
        let token = self.peek();

        if token.is_none() {
            return Ok(None);
        }

        let variant = match token.unwrap().kind {
            TokenKind::Amp => {
                self.next_token();

                // @@TODO: raw_refs...
                match self.parse_type()? {
                    Some(ty) => Type::Ref(ty),
                    None => return Ok(None),
                }
            }
            TokenKind::Question => {
                self.next_token();
                Type::Existential
            }
            // TODO: bracketed types...
            TokenKind::Ident(id) => {
                self.next_token();

                let (name, args) = self.parse_name_with_type_args(&id)?;
                // if the type_args are None, this means that the name could be either a
                // infer_type, or a type_var...
                match args {
                    Some(type_args) => Type::Named(NamedType { name, type_args }),
                    None => {
                        // @@Cleanup: This produces an AstNode<AccessName> whereas we just want the single name...
                        let location = name.location();
                        let ident = name.body().path.get(0).unwrap();

                        match IDENTIFIER_MAP.ident_name(*ident).as_str() {
                            "_" => Type::Infer,
                            // @@TypeArgsNaming: Here the rules are built-in for what the name of a type-arg is,
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
                                        type_args: vec![],
                                    })
                                }
                            }
                        }
                    }
                }
            }
            _ => return Ok(None),
        };

        Ok(Some(AstNode::new(
            variant,
            start.join(self.current_location()),
        )))
    }

    pub fn parse_name_or_infix_call(&self) -> ParseResult<AstNode<Expression>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Dot));

        let start = self.current_location();

        match &self.next_token() {
            Some(Token {
                kind: TokenKind::Ident(id),
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
                    let mut args = AstNode::new(FunctionCallArgs { entries: vec![] }, *span);

                    // so we know that this is the beginning of the function call, so we have to essentially parse an arbitrary number
                    // of expressions separated by commas as arguments to the call.
                    let gen = self.from_stream(stream.to_owned(), *span);

                    while gen.has_token() {
                        let arg = gen.parse_expression_bp(0);
                        args.entries.push(arg?);

                        // now we eat the next token, checking that it is a comma
                        match gen.peek() {
                            Some(token) if token.has_kind(TokenKind::Comma) => gen.next_token(),
                            _ => break,
                        };
                    }

                    Ok(self.node_with_location(
                        Expression::new(ExpressionKind::FunctionCall(FunctionCallExpr {
                            subject: self.make_ident_from_id(id, *id_span),
                            args,
                        })),
                        start.join(self.current_location()),
                    ))
                }
                _ => Ok(self.make_ident_from_id(id, *id_span)),
            },
            _ => Err(ParseError::Parsing {
                message: "Expecting field name after property access.".to_string(),
                src: self.source_location(&self.current_location()),
            }),
        }
    }

    pub fn parse_block_or_braced_literal(
        &self,
        tree: &[Token],
        span: &Location,
    ) -> ParseResult<AstNode<Expression>> {
        let _gen = self.from_stream(tree.to_owned(), *span);
        todo!()
    }

    pub fn parse_pattern(&self) -> ParseResult<AstNode<Pattern>> {
        todo!()
    }

    /// Function to either parse an expression that is wrapped in parentheses or a tuple literal. If this
    /// is a tuple literal, the first expression must be followed by a comma separator, after that the comma
    /// after the expression is optional.
    ///
    ///
    /// Tuples have a familiar syntax with many other languages, but exhibit two distinct differences between the common syntax. These differences are:
    ///
    /// - Empty tuples: (,)
    /// - Singleton tuple : (A,)
    /// - Many membered tuple: (A, B, C) or (A, B, C,)
    ///
    pub fn parse_expression_or_tuple(
        &self,
        tree: &[Token],
        span: &Location,
    ) -> ParseResult<AstNode<Expression>> {
        let gen = self.from_stream(tree.to_owned(), *span);
        let start = self.current_location();

        match gen.peek() {
            // Handle the empty tuple case
            Some(token) if token.has_kind(TokenKind::Comma) => {
                gen.next_token();

                if gen.has_token() {
                    return Err(ParseError::Parsing {
                        message: "Unexpected comma in the place of a expression".to_string(),
                        src: gen.source_location(&start),
                    });
                }

                return Ok(AstNode::new(
                    Expression::new(ExpressionKind::LiteralExpr(AstNode::new(
                        Literal::Tuple(TupleLiteral { elements: vec![] }),
                        start.join(gen.current_location()),
                    ))),
                    start.join(gen.current_location()),
                ));
            }
            // this is then either an wrapped expression or a tuple literal with multiple elements.
            Some(_) => (),
            None => todo!(), // Function body
        };

        let expr = gen.parse_expression_bp(0)?;
        let mut elements = iter::once(expr.clone()).collect::<Vec<_>>();
        let mut is_tuple = false;

        loop {
            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    is_tuple = true;
                    gen.next_token();

                    // Handles the case where this is a trailing comma and no tokens after...
                    if !gen.has_token() {
                        break;
                    }

                    elements.push(gen.parse_expression_bp(0)?)
                }
                Some(_) => {
                    return Err(ParseError::Parsing {
                        message: "Unexpected comma in the place of a expression".to_string(),
                        src: gen.source_location(&start),
                    })
                }
                None if is_tuple => break,
                None => return Ok(expr),
            }
        }

        Ok(AstNode::new(
            Expression::new(ExpressionKind::LiteralExpr(AstNode::new(
                Literal::Tuple(TupleLiteral { elements }),
                start.join(gen.current_location()),
            ))),
            start.join(gen.current_location()),
        ))
    }

    pub fn parse_array_literal(
        &self,
        tree: &[Token],
        span: &Location,
    ) -> ParseResult<AstNode<Expression>> {
        let gen = self.from_stream(tree.to_owned(), *span);
        let start = gen.current_location();

        let mut elements = vec![];

        while gen.has_token() {
            let expr = gen.parse_expression_bp(0)?;
            elements.push(expr);

            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
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

        Ok(AstNode::new(
            Expression::new(ExpressionKind::LiteralExpr(AstNode::new(
                Literal::List(ListLiteral { elements }),
                start.join(gen.current_location()),
            ))),
            start.join(gen.current_location()),
        ))
    }

    /// Convert the current token (provided it is a primitive literal) into a [ExpressionKind::LiteralExpr]
    /// by simply matching on the type of the expr.
    pub fn parse_literal(&self) -> AstNode<Expression> {
        let token = self.current_token();
        let literal = AstNode::new(
            match token.kind {
                TokenKind::IntLiteral(num) => Literal::Int(num),
                TokenKind::FloatLiteral(num) => Literal::Float(num),
                TokenKind::CharLiteral(ch) => Literal::Char(ch),
                TokenKind::StrLiteral(_str) => {
                    panic!("StringLiteral ids haven't been implemented yet!")
                } //Literal::Str(str),
                _ => unreachable!(),
            },
            token.span,
        );

        AstNode::new(
            Expression::new(ExpressionKind::LiteralExpr(literal)),
            token.span,
        )
    }
}
