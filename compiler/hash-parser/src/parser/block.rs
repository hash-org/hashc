//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_reporting::diagnostic::{AccessToDiagnosticsMut, DiagnosticsMut};
use hash_token::{delimiter::Delimiter, keyword::Keyword, TokenKind};

use super::{AstGen, ParseResult};
use crate::diagnostics::error::ParseErrorKind;

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a block.
    #[inline]
    pub(crate) fn parse_block(&mut self) -> ParseResult<AstNode<Block>> {
        let mut gen = self.parse_delim_tree(Delimiter::Brace, Some(ParseErrorKind::Block))?;

        let block = gen.parse_body_block_inner();
        self.diagnostics.merge_diagnostics(gen.diagnostics);

        Ok(self.node_with_span(Block::Body(block), self.current_pos()))
    }

    /// Helper function to simply parse a body block without wrapping it in
    /// [Block].
    #[inline]
    pub(crate) fn parse_body_block(&mut self) -> ParseResult<AstNode<BodyBlock>> {
        let mut gen = self.parse_delim_tree(Delimiter::Brace, Some(ParseErrorKind::Block))?;

        let block = gen.parse_body_block_inner();
        self.merge_diagnostics(gen.diagnostics);

        Ok(self.node_with_span(block, self.current_pos()))
    }

    /// Parse a body block that uses itself as the inner generator. This
    /// function will advance the current generator than expecting that the
    /// next token is a brace tree.
    pub(crate) fn parse_body_block_inner(&mut self) -> BodyBlock {
        // Append the initial statement if there is one.
        let start = self.current_pos();
        let mut block = BodyBlock { statements: AstNodes::empty(self.span()), expr: None };

        // Just return an empty block if we don't get anything
        if !self.has_token() {
            return block;
        }

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
                block.statements.nodes.push(expr)
            } else {
                // update the `statements` span to reflect the true span of the statements
                // that were parsed
                let span = self.make_span(start.join(next_location));
                block.statements.set_span(span);
                block.expr = Some(expr)
            }
        }

        block
    }

    /// Parse a `for` loop block.
    pub(crate) fn parse_for_loop(&mut self) -> ParseResult<AstNode<Block>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::For)));

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
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::While)));

        let start = self.current_pos();

        let condition = self.parse_expr_with_precedence(0)?;
        let while_body = self.parse_block()?;

        Ok(self
            .node_with_joined_span(Block::While(WhileLoopBlock { condition, while_body }), start))
    }

    /// Parse a match case. A match case involves handling the pattern and the
    /// expression branch.
    pub(crate) fn parse_match_case(&mut self) -> ParseResult<AstNode<MatchCase>> {
        let start = self.current_pos();
        let pattern = self.parse_pat()?;

        self.parse_arrow()?;
        let expr = self.parse_expr_with_precedence(0)?;

        Ok(self.node_with_joined_span(MatchCase { pat: pattern, expr }, start))
    }

    /// Parse a match block statement, which is composed of a subject and an
    /// arbitrary number of match cases that are surrounded in braces.
    pub(crate) fn parse_match_block(&mut self) -> ParseResult<AstNode<Block>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Match)));

        let start = self.current_pos();
        let subject = self.parse_expr_with_precedence(0)?;

        let mut gen = self.parse_delim_tree(Delimiter::Brace, None)?;
        let cases =
            gen.parse_separated_fn(|g| g.parse_match_case(), |g| g.parse_token(TokenKind::Comma));
        self.consume_gen(gen);

        Ok(self.node_with_joined_span(
            Block::Match(MatchBlock { subject, cases, origin: MatchOrigin::Match }),
            start,
        ))
    }

    /// Parse an `if-block` collection.
    pub(crate) fn parse_if_block(&mut self) -> ParseResult<AstNode<Block>> {
        debug_assert!(matches!(self.current_token().kind, TokenKind::Keyword(Keyword::If)));

        let start = self.current_pos();

        let mut clauses = vec![];
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
                clauses: self.nodes_with_span(clauses, start.join(if_span)),
                otherwise: otherwise_clause,
            }),
            start,
        ))
    }
}
