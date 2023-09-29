//! Hash Compiler parser sources. This module contains logic for parsing
//! operators from the provided token source.
use hash_ast::ast::*;
use hash_token::{keyword::Keyword, TokenKind};

use super::AstGen;

impl<'s> AstGen<'s> {
    /// This function is used to pickup 'glued' operator tokens to form more
    /// complex binary operators that might be made up of multiple tokens.
    /// The function will peek ahead (2 tokens at most since all binary
    /// operators are made of that many tokens). The function returns an
    /// optional derived operator, and the number of tokens that was
    /// consumed deriving the operator, it is the responsibility
    /// of the caller to increment the token stream by the provided number.
    pub(crate) fn parse_binary_operator(&self) -> (Option<BinOp>, u8) {
        let token = self.peek();

        // check if there is a token that we can peek at ahead...
        if token.is_none() {
            return (None, 0);
        }

        match &(token.unwrap()).kind {
            // Since the 'as' keyword is also a binary operator, we have to handle it here...
            TokenKind::Keyword(Keyword::As) => (Some(BinOp::As), 1),
            TokenKind::Tilde => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (None, 0), // merge declaration
                _ => (Some(BinOp::Merge), 1),
            },
            TokenKind::Eq => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(BinOp::EqEq), 2),
                _ => (None, 0),
            },
            TokenKind::Lt => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(BinOp::LtEq), 2),
                Some(token) if token.kind == TokenKind::Lt => (Some(BinOp::Shl), 2),
                _ => (Some(BinOp::Lt), 1),
            },
            TokenKind::Gt => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(BinOp::GtEq), 2),
                Some(token) if token.kind == TokenKind::Gt => (Some(BinOp::Shr), 2),
                _ => (Some(BinOp::Gt), 1),
            },
            TokenKind::Plus => (Some(BinOp::Add), 1),
            TokenKind::Minus => (Some(BinOp::Sub), 1),
            TokenKind::Star => (Some(BinOp::Mul), 1),
            TokenKind::Slash => (Some(BinOp::Div), 1),
            TokenKind::Percent => (Some(BinOp::Mod), 1),
            TokenKind::Caret => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Caret => (Some(BinOp::Exp), 2),
                _ => (Some(BinOp::BitXor), 1),
            },
            TokenKind::Amp => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Amp => (Some(BinOp::And), 2),
                _ => (Some(BinOp::BitAnd), 1),
            },
            TokenKind::Pipe => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Pipe => (Some(BinOp::Or), 2),
                _ => (Some(BinOp::BitOr), 1),
            },
            TokenKind::Exclamation => match self.peek_second() {
                Some(token) if token.kind == TokenKind::Eq => (Some(BinOp::NotEq), 2),
                _ => (None, 0), // this is a unary operator '!'
            },
            _ => (None, 0),
        }
    }

    /// Function to parse a [BinTyOp] which returns a type operator if one is
    /// present, and the number of tokens consumed. If no type operator follows,
    /// then the consumed tokens count will be 0.
    pub(crate) fn parse_ty_op(&self) -> (Option<BinTyOp>, u8) {
        match self.peek() {
            Some(token) if token.has_kind(TokenKind::Pipe) => (Some(BinTyOp::Union), 1),
            Some(token) if token.has_kind(TokenKind::Tilde) => (Some(BinTyOp::Equality), 1),
            _ => (None, 0),
        }
    }
}
