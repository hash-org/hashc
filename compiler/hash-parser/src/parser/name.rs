//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_token::{Token, TokenKind};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a singular [Name] from the current token stream.
    #[inline]
    pub fn parse_name(&self) -> AstGenResult<AstNode<Name>> {
        self.parse_name_with_error(AstGenErrorKind::ExpectedIdentifier)
    }

    /// Parse a singular [Name] from the current token stream.
    #[inline]
    pub fn parse_name_with_error(&self, err: AstGenErrorKind) -> AstGenResult<AstNode<Name>> {
        match self.next_token() {
            Some(Token { kind: TokenKind::Ident(ident), span }) => {
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
