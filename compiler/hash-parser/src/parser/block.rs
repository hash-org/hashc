//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_reporting::diagnostic::HasDiagnosticsMut;
use hash_token::{delimiter::Delimiter, keyword::Keyword, TokenKind};
use hash_utils::thin_vec::thin_vec;

use super::{AstGen, ParseResult};
use crate::diagnostics::error::ParseErrorKind;

impl AstGen<'_> {
    /// Parse a block.
    #[inline]
    pub(crate) fn parse_block(&mut self) -> ParseResult<AstNode<Block>> {
        let (block, span) =
            self.in_tree(Delimiter::Brace, Some(ParseErrorKind::ExpectedBlock), |g| {
                Ok((g.parse_body_block_inner(), g.range()))
            })?;

        Ok(self.node_with_span(Block::Body(block), span))
    }

    /// Parse a body block that uses itself as the inner generator. This
    /// function will advance the current generator than expecting that the
    /// next token is a brace tree.
    pub(crate) fn parse_body_block_inner(&mut self) -> BodyBlock {
        // Just return an empty block if we don't get anything
        if !self.has_token() {
            return BodyBlock {
                statements: self.nodes_with_span(thin_vec![], self.range()),
                expr: None,
            };
        }

        // Append the initial statement if there is one.
        let mut block_span = self.current_pos();
        let mut statements = thin_vec![];
        let mut block_expr = None;

        // firstly check if the first token signals a beginning of a statement, we can
        // tell this by checking for keywords that must begin a statement...
        while self.has_token() {
            let next_location = self.current_pos();

            let (semi, expr) = match self.parse_top_level_expr() {
                Ok(Some(res)) => res,
                Ok(_) => continue,
                // @@Future: attempt to recover here to see if we can get a semi, and then reset
                Err(err) => {
                    self.add_error(err);
                    break;
                }
            };

            if semi || self.peek().is_some() {
                statements.push(expr)
            } else {
                // update the `statements` span to reflect the true span of the statements
                // that were parsed
                block_span = block_span.join(next_location);
                block_expr = Some(expr);
            }
        }

        BodyBlock { statements: self.nodes_with_span(statements, block_span), expr: block_expr }
    }

    /// Parse a `for` loop block.
    pub(crate) fn parse_for_loop(&mut self) -> ParseResult<AstNode<Block>> {
        self.skip_fast(TokenKind::Keyword(Keyword::For)); // `for`

        let start = self.current_pos();

        // now we parse the singular pattern that begins at the for-loop
        let pattern = self.parse_singular_pat()?;

        self.parse_token(TokenKind::Keyword(Keyword::In))?;

        let iterator = self.parse_expr_with_precedence(0)?;
        let body = self.parse_block()?;

        Ok(self.node_with_joined_span(
            Block::For(ForLoopBlock { pat: pattern, iterator, for_body: body }),
            start,
        ))
    }

    /// Parse a `while` loop block.
    pub(crate) fn parse_while_loop(&mut self) -> ParseResult<AstNode<Block>> {
        let start = self.current_pos();
        self.skip_fast(TokenKind::Keyword(Keyword::While)); // `while`

        let condition = self.parse_expr_with_precedence(0)?;
        let while_body = self.parse_block()?;

        Ok(self
            .node_with_joined_span(Block::While(WhileLoopBlock { condition, while_body }), start))
    }

    /// Parse a match case. A match case involves handling the pattern and the
    /// expression branch.
    pub(crate) fn parse_match_case(&mut self) -> ParseResult<AstNode<MatchCase>> {
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;
        let start = self.current_pos();

        let pat = self.parse_pat()?;
        self.parse_token(TokenKind::FatArrow)?;
        let expr = self.parse_expr_with_precedence(0)?;

        Ok(self.node_with_joined_span(MatchCase { pat, expr, macros }, start))
    }

    /// Parse a match block statement, which is composed of a subject and an
    /// arbitrary number of match cases that are surrounded in braces.
    pub(crate) fn parse_match_block(&mut self) -> ParseResult<AstNode<Block>> {
        let start = self.current_pos();
        self.skip_fast(TokenKind::Keyword(Keyword::Match)); // `match`

        let subject = self.parse_expr_with_precedence(0)?;

        let cases = self.in_tree(Delimiter::Brace, None, |g| {
            Ok(g.parse_nodes(|g| g.parse_match_case(), |g| g.parse_token(TokenKind::Comma)))
        })?;

        Ok(self.node_with_joined_span(
            Block::Match(MatchBlock { subject, cases, origin: MatchOrigin::Match }),
            start,
        ))
    }

    /// Parse an `if-block` collection.
    pub(crate) fn parse_if_block(&mut self) -> ParseResult<AstNode<Block>> {
        let start = self.current_pos();
        self.skip_fast(TokenKind::Keyword(Keyword::If)); // `if`

        let mut clauses = thin_vec![];
        let mut otherwise_clause = None;
        let mut if_span = self.current_pos();

        while self.has_token() {
            if_span = self.current_pos();
            let condition = self.parse_expr_with_precedence(0)?;
            let body = self.parse_block()?;

            clauses
                .push(self.node_with_joined_span(IfClause { condition, if_body: body }, if_span));

            // Now check if there is another branch after the else or if, and loop
            // onwards...
            match self.peek_kind() {
                Some(TokenKind::Keyword(Keyword::Else)) => {
                    self.skip_fast(TokenKind::Keyword(Keyword::Else)); // `else`

                    // skip trying to convert just an 'else' branch since this is another
                    // if-branch
                    if let Some(TokenKind::Keyword(Keyword::If)) = self.peek_kind() {
                        self.skip_fast(TokenKind::Keyword(Keyword::If)); // `if`
                        continue;
                    }

                    otherwise_clause = Some(self.parse_block()?);
                    break;
                }
                _ => break,
            };
        }

        let clauses = self.nodes_with_span(clauses, start.join(if_span));
        Ok(self.node_with_joined_span(
            Block::If(IfBlock { clauses, otherwise: otherwise_clause }),
            start,
        ))
    }
}
