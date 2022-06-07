//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_alloc::row;
use hash_ast::{ast::*, ast_nodes};
use hash_source::location::Span;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// Parse a block.
    pub(crate) fn parse_block(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        let (gen, start) = match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            }) => {
                self.skip_token(); // step-along since we matched a block...

                let tree = self.token_trees.get(*tree_index).unwrap();

                (self.from_stream(tree, self.current_location()), *span)
            }
            token => self.error_with_location(
                AstGenErrorKind::Block,
                None,
                token.map(|t| t.kind),
                token.map_or_else(|| self.next_location(), |t| t.span),
            )?,
        };

        self.parse_block_from_gen(&gen, start, None)
    }

    /// Function to parse a block body
    pub(crate) fn parse_block_from_gen(
        &self,
        gen: &Self,
        start: Span,
        initial_statement: Option<AstNode<'c, Expression<'c>>>,
    ) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
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
            return Ok(self.node_with_span(Block::Body(block), start));
        }

        // firstly check if the first token signals a beginning of a statement, we can tell
        // this by checking for keywords that must begin a statement...
        while gen.has_token() {
            let (has_semi, statement) = gen.parse_top_level_expression(false)?;

            match (has_semi, gen.peek()) {
                (true, _) => block.statements.nodes.push(statement, &self.wall),
                (false, Some(token)) => gen.error(
                    AstGenErrorKind::Expected,
                    Some(TokenKindVector::from_row(row![&self.wall; TokenKind::Semi])),
                    Some(token.kind),
                )?,
                (false, None) => block.expr = Some(statement),
            }
        }

        Ok(self.node_with_joined_span(Block::Body(block), &start))
    }

    /// Parse a `for` loop block.
    pub(crate) fn parse_for_loop(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::For)));

        let start = self.current_location();

        // now we parse the singular pattern that begins at the for-loop
        let pattern = self.parse_singular_pattern()?;

        self.parse_token(TokenKind::Keyword(Keyword::In))?;

        let iterator = self.parse_expression_with_precedence(0)?;
        let body = self.parse_block()?;

        Ok(self.node_with_joined_span(
            Block::For(ForLoopBlock {
                pattern,
                iterator,
                body,
            }),
            &start,
        ))
    }

    /// Parse a `while` loop block.
    pub(crate) fn parse_while_loop(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::While)));

        let start = self.current_location();

        let condition = self.parse_expression_with_precedence(0)?;
        let body = self.parse_block()?;

        Ok(self.node_with_joined_span(Block::While(WhileLoopBlock { condition, body }), &start))
    }

    /// Parse a match case. A match case involves handling the pattern and the
    /// expression branch.
    pub(crate) fn parse_match_case(&self) -> AstGenResult<'c, AstNode<'c, MatchCase<'c>>> {
        let start = self.current_location();
        let pattern = self.parse_pattern()?;

        self.parse_arrow()?;
        let expr = self.parse_expression_with_precedence(0)?;

        Ok(self.node_with_joined_span(MatchCase { pattern, expr }, &start))
    }

    /// Parse a match block statement, which is composed of a subject and an arbitrary
    /// number of match cases that are surrounded in braces.
    pub(crate) fn parse_match_block(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Match)));

        let start = self.current_location();
        let subject = self.parse_expression_with_precedence(0)?;

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

                    gen.parse_token(TokenKind::Semi)?;
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

        Ok(self.node_with_joined_span(
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
    pub(crate) fn parse_if_block(&self) -> AstGenResult<'c, AstNode<'c, Block<'c>>> {
        debug_assert!(matches!(
            self.current_token().kind,
            TokenKind::Keyword(Keyword::If)
        ));

        let start = self.current_location();

        let mut cases = AstNodes::empty();
        let mut has_else_branch = false;

        while self.has_token() {
            let clause = self.parse_expression_with_precedence(0)?;

            let branch = self.parse_block()?;
            let (clause_span, branch_span) = (clause.span(), branch.span());

            cases.nodes.push(
                self.node_with_span(
                    MatchCase {
                        pattern: self.node_with_span(
                            Pattern::If(IfPattern {
                                pattern: self
                                    .node_with_span(Pattern::Ignore(IgnorePattern), clause_span),
                                condition: clause,
                            }),
                            clause_span,
                        ),
                        expr: self.node_with_span(
                            Expression::new(ExpressionKind::Block(BlockExpr(branch))),
                            branch_span,
                        ),
                    },
                    clause_span.join(branch_span),
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
                    let else_span = start.join(else_branch.span());

                    has_else_branch = true;

                    cases.nodes.push(
                        self.node_with_span(
                            MatchCase {
                                pattern: self.node(Pattern::Ignore(IgnorePattern)),
                                expr: self.node_with_span(
                                    Expression::new(ExpressionKind::Block(BlockExpr(else_branch))),
                                    else_span,
                                ),
                            },
                            else_span,
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

        Ok(self.node_with_joined_span(
            Block::Match(MatchBlock {
                subject: self.make_bool(true),
                cases,
                origin: MatchOrigin::If,
            }),
            &start,
        ))
    }
}
