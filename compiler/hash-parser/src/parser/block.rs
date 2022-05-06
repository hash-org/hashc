//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_alloc::row;
use hash_ast::{ast::*, ast_nodes};
use hash_source::location::Location;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
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
                self.error_with_location(AstGenErrorKind::Block, None, None, self.next_location())?
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

            let (has_semi, statement) = gen.parse_general_statement(false)?;

            match (has_semi, gen.peek()) {
                (true, _) => block.statements.nodes.push(statement, &self.wall),
                (false, Some(token)) => gen.error(
                    AstGenErrorKind::Expected,
                    Some(TokenKindVector::from_row(row![&self.wall; TokenKind::Semi])),
                    Some(token.kind),
                )?,
                (false, None) => {
                    let span = statement.location();

                    match statement.into_body().move_out() {
                        Statement::Block(BlockStatement(inner_block)) => {
                            block.expr = Some(self.node_with_location(
                                Expression::new(ExpressionKind::Block(BlockExpr(inner_block))),
                                span,
                            ));
                        }
                        Statement::Expr(ExprStatement(expr)) => {
                            block.expr = Some(expr);
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }

        Ok(self.node_with_joined_location(Block::Body(block), &start))
    }

    /// Parse a for-loop block
    pub fn parse_for_loop(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::For)));

        let start = self.current_location();

        // now we parse the singular pattern that begins at the for-loop
        let pattern = self.parse_declaration_pattern()?;
        let pattern_location = pattern.location();

        self.parse_token_atom(TokenKind::Keyword(Keyword::In))?;

        self.disallow_struct_literals.set(true);
        let iterator = self.parse_expression_with_precedence(0)?;
        let iterator_location = iterator.location();
        self.disallow_struct_literals.set(false);

        let body = self.parse_block()?;
        let body_location = body.location();

        // transpile the for-loop into a simpler loop as described by the documentation.
        // Since for loops are used for iterators in hash, we transpile the construct into a primitive loop.
        // An iterator can be traversed by calling the next function on the iterator.
        // Since next returns a Option type, we need to check if there is a value or if it returns None.
        // If a value does exist, we essentially perform an assignment to the pattern provided.
        // If None, the branch immediately breaks the for loop.
        //
        // A rough outline of what the transpilation process for a for loop looks like:
        //
        // For example, the for loop can be expressed using loop as:
        //
        // >>> for <pat> in <iterator> {
        // >>>     <block>
        // >>> }
        //
        // converted to:
        // >>> loop {
        // >>>     match next(<iterator>) {
        // >>>         Some(<pat>) => <block>;
        // >>>         None        => break;
        // >>>     }
        // >>> }
        //
        Ok(self.node_with_joined_location(Block::Loop(LoopBlock(self.node_with_location(
            Block::Match(MatchBlock {
            subject: self.node(Expression::new(ExpressionKind::FunctionCall(
                FunctionCallExpr {
                    subject: self.node(Expression::new(ExpressionKind::Variable(
                        VariableExpr {
                            name: self.make_access_name_from_str("next", iterator.location()),
                            type_args: AstNodes::empty(),
                        },
                    ))),
                    args: self.node_with_location(FunctionCallArgs {
                        entries: ast_nodes![&self.wall; self.node_with_location(
                            FunctionCallArg {
                                name: None,
                                value: iterator,
                            },
                            iterator_location
                        )],
                    }, iterator_location),
                },
            ))),
            cases: ast_nodes![&self.wall; self.node_with_location(MatchCase {
                    pattern: self.node_with_location(
                        Pattern::Enum(
                            EnumPattern {
                                name:
                                    self.make_access_name_from_str(
                                        "Some",
                                        self.current_location()
                                    ),
                                fields: ast_nodes![&self.wall; pattern],
                            },
                        ), pattern_location
                    ),
                    expr: self.node_with_location(Expression::new(ExpressionKind::Block(BlockExpr(body))), body_location),
                }, start),
                self.node(MatchCase {
                    pattern: self.node(
                        Pattern::Enum(
                            EnumPattern {
                                name:
                                    self.make_access_name_from_str(
                                        "None",
                                        self.current_location()
                                    ),
                                fields: AstNodes::empty(),
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
            origin: MatchOrigin::For
        }), start))), &start))
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
        self.disallow_struct_literals.set(false);

        let body = self.parse_block()?;
        let body_location = body.location();
        let condition_location = condition.location();

        Ok(self.node_with_joined_location(
            Block::Loop(LoopBlock(self.node_with_location(
                Block::Match(MatchBlock {
                    subject: condition,
                    cases: ast_nodes![&self.wall; self.node(MatchCase {
                        pattern: self.node(Pattern::Binding(BindingPattern(
                            self.make_ident_from_str("true", body_location)
                        ))),
                            expr: self.node(Expression::new(ExpressionKind::Block(BlockExpr(body)))),
                        }),
                        self.node(MatchCase {
                            pattern: self.node(Pattern::Binding(BindingPattern(
                                self.make_ident_from_str("false", body_location)
                            ))),
                            expr: self.node(Expression::new(ExpressionKind::Block(BlockExpr(
                                self.node(Block::Body(BodyBlock {
                                    statements: ast_nodes![&self.wall; self.node(Statement::Break(BreakStatement))],
                                    expr: None,
                                })),
                            )))),
                        }),
                    ],
                    origin: MatchOrigin::While
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

        Ok(self.node_with_joined_location(MatchCase { pattern, expr }, &start))
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

        Ok(self.node_with_joined_location(
            Block::Match(MatchBlock {
                subject,
                cases,
                origin: MatchOrigin::Match,
            }),
            &start,
        ))
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
                self.node_with_location(
                    MatchCase {
                        pattern: self.node_with_location(
                            Pattern::If(IfPattern {
                                pattern: self
                                    .node_with_location(Pattern::Ignore(IgnorePattern), clause_loc),
                                condition: clause,
                            }),
                            clause_loc,
                        ),
                        expr: self.node_with_location(
                            Expression::new(ExpressionKind::Block(BlockExpr(branch))),
                            branch_loc,
                        ),
                    },
                    clause_loc.join(branch_loc),
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
                        self.node_with_location(
                            MatchCase {
                                pattern: self.node(Pattern::Ignore(IgnorePattern)),
                                expr: self.node_with_location(
                                    Expression::new(ExpressionKind::Block(BlockExpr(else_branch))),
                                    loc,
                                ),
                            },
                            loc,
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

        Ok(self.node_with_joined_location(
            Block::Match(MatchBlock {
                subject: self.make_ident("true", &self.current_location()),
                cases,
                origin: MatchOrigin::If,
            }),
            &start,
        ))
    }
}
