//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::identifier::CORE_IDENTIFIERS;
use hash_token::{Token, TokenKind};

use super::AstGen;
use crate::diagnostics::error::{ParseErrorKind, ParseResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a singular [Name] from the current token stream.
    #[inline]
    pub fn parse_name(&self) -> ParseResult<AstNode<Name>> {
        self.parse_name_with_error(ParseErrorKind::ExpectedName)
    }

    /// Parse a singular [Name] from the current token stream. The function
    /// disallows a [Name] to be the special binding `_`.
    #[inline]
    pub fn parse_name_with_error(&self, err: ParseErrorKind) -> ParseResult<AstNode<Name>> {
        match self.next_token() {
            Some(Token { kind: TokenKind::Ident(ident), span })
                if *ident != CORE_IDENTIFIERS.underscore =>
            {
                Ok(self.node_with_span(Name { ident: *ident }, *span))
            }
            token => self.error_with_location(
                err,
                None,
                None,
                token.map(|tok| tok.span).unwrap_or_else(|| self.next_location()),
            ),
        }
    }
}
