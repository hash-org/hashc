//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::identifier::Identifier;
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

    /// Parse an [Namespace] from the current token stream. An [Namespace] is
    /// defined as a number of identifiers that are separated by the
    /// namespace operator '::'. The function presumes that the current
    /// token is an identifier an that the next token is a colon.
    pub fn parse_ns(&self, start_id: AstNode<Identifier>) -> AstGenResult<AstNode<Namespace>> {
        let start = self.current_location();
        let mut path = vec![start_id];

        loop {
            match (self.peek(), self.peek_second()) {
                (Some(tok), Some(second_tok))
                    if tok.has_kind(TokenKind::Colon) && second_tok.has_kind(TokenKind::Colon) =>
                {
                    self.offset.update(|current| current + 2); // '::'

                    match self.peek() {
                        Some(Token { kind: TokenKind::Ident(id), span }) => {
                            self.skip_token();
                            path.push(self.node_with_span(*id, *span));
                        }
                        token => self.error_with_location(
                            AstGenErrorKind::Namespace,
                            None,
                            token.map(|tok| tok.kind),
                            token.map_or_else(|| self.current_location(), |tok| tok.span),
                        )?,
                    }
                }
                _ => break,
            }
        }

        let location = start.join(self.current_location());

        Ok(self.node_with_span(Namespace { path: AstNodes::new(path, Some(location)) }, location))
    }
}
