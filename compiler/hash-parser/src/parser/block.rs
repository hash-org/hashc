//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_token::{delimiter::Delimiter, keyword::Keyword, TokenKind, TokenKindVector};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a block.
    #[inline]
    pub(crate) fn parse_block(&self) -> AstGenResult<AstNode<Block>> {
        let gen = self.parse_delim_tree(Delimiter::Brace, Some(AstGenErrorKind::Block))?;

        Ok(self.node_with_span(Block::Body(gen.parse_body_block_inner()?), self.current_location()))
    }

    /// Helper function to simply parse a body block without wrapping it in
    /// [Block].
    #[inline]
    pub(crate) fn parse_body_block(&self) -> AstGenResult<AstNode<BodyBlock>> {
        let gen = self.parse_delim_tree(Delimiter::Brace, Some(AstGenErrorKind::Block))?;

        Ok(self.node_with_span(gen.parse_body_block_inner()?, self.current_location()))
    }

    /// Parse a body block that uses itself as the inner generator. This
    /// function will advance the current generator than expecting that the
    /// next token is a brace tree.
    pub(crate) fn parse_body_block_inner(&self) -> AstGenResult<BodyBlock> {
        // Append the initial statement if there is one.
        let mut block = BodyBlock { statements: AstNodes::empty(), expr: None };

        // Just return an empty block if we don't get anything
        if !self.has_token() {
            return Ok(block);
        }

        // firstly check if the first token signals a beginning of a statement, we can
        // tell this by checking for keywords that must begin a statement...
        while self.has_token() {
            let (has_semi, statement) = self.parse_top_level_expr(false)?;

            match (has_semi, self.peek()) {
                (true, _) => block.statements.nodes.push(statement),
                (false, Some(token)) => self.error(
                    AstGenErrorKind::Expected,
                    Some(TokenKindVector::singleton(TokenKind::Semi)),
                    Some(token.kind),
                )?,
                (false, None) => block.expr = Some(statement),
            }
        }

        Ok(block)
    }

    /// Parse a `for` loop block.
    pub(crate) fn parse_for_loop(&self) -> AstGenResult<AstNode<Block>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::For)));

        let start = self.current_location();

        // now we parse the singular pattern that begins at the for-loop
        let pattern = self.parse_singular_pat()?;

        self.parse_token(TokenKind::Keyword(Keyword::In))?;

        let iterator = self.parse_expr_with_precedence(0)?;
        let body = self.parse_block()?;

        Ok(self.node_with_joined_span(
            Block::For(ForLoopBlock { pat: pattern, iterator, body }),
            &start,
        ))
    }

    /// Parse a `while` loop block.
    pub(crate) fn parse_while_loop(&self) -> AstGenResult<AstNode<Block>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::While)));

        let start = self.current_location();

        let condition = self.parse_expr_with_precedence(0)?;
        let body = self.parse_block()?;

        Ok(self.node_with_joined_span(Block::While(WhileLoopBlock { condition, body }), &start))
    }

    /// Parse a match case. A match case involves handling the pattern and the
    /// expression branch.
    pub(crate) fn parse_match_case(&self) -> AstGenResult<AstNode<MatchCase>> {
        let start = self.current_location();
        let pattern = self.parse_pat()?;

        self.parse_arrow()?;
        let expr = self.parse_expr_with_precedence(0)?;

        Ok(self.node_with_joined_span(MatchCase { pat: pattern, expr }, &start))
    }

    /// Parse a match block statement, which is composed of a subject and an
    /// arbitrary number of match cases that are surrounded in braces.
    pub(crate) fn parse_match_block(&self) -> AstGenResult<AstNode<Block>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Match)));

        let start = self.current_location();
        let subject = self.parse_expr_with_precedence(0)?;

        let mut cases = AstNodes::empty();

        let gen = self.parse_delim_tree(Delimiter::Brace, None)?;

        while gen.has_token() {
            cases.nodes.push(gen.parse_match_case()?);
            gen.parse_token(TokenKind::Semi)?;
        }

        Ok(self.node_with_joined_span(
            Block::Match(MatchBlock { subject, cases, origin: MatchOrigin::Match }),
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
    /// empty block since an if-block could be assigned to any variable and
    /// therefore we need to know the outcome of all branches for
    /// typechecking.
    pub(crate) fn parse_if_block(&self) -> AstGenResult<AstNode<Block>> {
        debug_assert!(matches!(self.current_token().kind, TokenKind::Keyword(Keyword::If)));

        let start = self.current_location();

        let mut clauses = vec![];
        let mut otherwise_clause = None;

        while self.has_token() {
            let if_span = self.current_location();

            clauses.push(self.node_with_joined_span(
                IfClause {
                    condition: self.parse_expr_with_precedence(0)?,
                    body: self.parse_block()?,
                },
                &if_span,
            ));

            // Now check if there is another branch after the else or if, and loop
            // onwards...
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Keyword(Keyword::Else)) => {
                    self.skip_token();

                    match self.peek() {
                        Some(token) if token.has_kind(TokenKind::Keyword(Keyword::If)) => {
                            // skip trying to convert just an 'else' branch since this is another
                            // if-branch
                            self.skip_token();
                            continue;
                        }
                        _ => (),
                    };

                    otherwise_clause = Some(self.parse_block()?);
                    break;
                }
                _ => break,
            };
        }

        Ok(self.node_with_joined_span(
            Block::If(IfBlock {
                clauses: AstNodes::new(clauses, None),
                otherwise: otherwise_clause,
            }),
            &start,
        ))
    }
}
