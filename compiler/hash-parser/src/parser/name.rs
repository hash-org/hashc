//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::identifier::IDENTS;
use hash_token::{Token, TokenKind};

use super::AstGen;
use crate::diagnostics::{
    error::{ParseErrorKind, ParseResult},
    expected::ExpectedItem,
};

impl<'s> AstGen<'s> {
    /// Parse a singular [Name] from the current token stream.
    #[inline]
    pub fn parse_name(&mut self) -> ParseResult<AstNode<Name>> {
        self.parse_name_with_error(ParseErrorKind::ExpectedName)
    }

    /// Parse a singular [Name] from the current token stream. The function
    /// disallows a [Name] to be the special binding `_`.
    #[inline]
    pub fn parse_name_with_error(&mut self, err: ParseErrorKind) -> ParseResult<AstNode<Name>> {
        match self.current_token_and_advance() {
            Some(Token { kind: TokenKind::Ident(ident), span }) if *ident != IDENTS.underscore => {
                Ok(self.node_with_span(Name { ident: *ident }, *span))
            }
            tok => self.err_with_location(
                err,
                ExpectedItem::Ident,
                None,
                tok.map(|tok| tok.span).unwrap_or_else(|| self.eof_pos()),
            ),
        }
    }

    /// Parse [PropertyKind::NamedField] which is used within [ExprKind::Access]
    /// as a named field. This function does not parse the
    /// [PropertyKind::NumericField] variant.
    #[inline]
    pub fn parse_named_field(&mut self, err: ParseErrorKind) -> ParseResult<AstNode<PropertyKind>> {
        match self.current_token_and_advance() {
            Some(Token { kind: TokenKind::Ident(ident), span }) if *ident != IDENTS.underscore => {
                Ok(self.node_with_span(PropertyKind::NamedField(*ident), *span))
            }
            token => self.err_with_location(
                err,
                ExpectedItem::Ident,
                None,
                token.map(|tok| tok.span).unwrap_or_else(|| self.eof_pos()),
            ),
        }
    }
}
