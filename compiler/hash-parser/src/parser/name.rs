//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_ast::ast::*;
use hash_source::identifier::Identifier;
use hash_token::{Token, TokenKind};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a singular [Name] from the current token stream.
    pub fn parse_name(&self) -> AstGenResult<AstNode<Name>> {
        match self.next_token() {
            Some(Token {
                kind: TokenKind::Ident(ident),
                span,
            }) => Ok(self.node_with_span(Name { ident: *ident }, *span)),
            _ => self.error(AstGenErrorKind::ExpectedIdentifier, None, None),
        }
    }

    /// Parse an [AccessName] from the current token stream. An [AccessName] is defined as
    /// a number of identifiers that are separated by the namespace operator '::'. The function
    /// presumes that the current token is an identifier an that the next token is a colon.
    pub fn parse_access_name(
        &self,
        start_id: AstNode<Identifier>,
    ) -> AstGenResult<AstNode<AccessName>> {
        let start = self.current_location();
        let mut path = vec![start_id];

        loop {
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Colon) => {
                    self.skip_token(); // :

                    match self.peek() {
                        Some(token) if token.has_kind(TokenKind::Colon) => {
                            self.skip_token(); // :

                            match self.peek() {
                                Some(Token {
                                    kind: TokenKind::Ident(id),
                                    span,
                                }) => {
                                    self.skip_token();
                                    path.push(self.node_with_span(*id, *span));
                                }
                                _ => self.error(AstGenErrorKind::AccessName, None, None)?,
                            }
                        }
                        _ => {
                            // backtrack the token count by one
                            self.offset.set(self.offset() - 1);
                            break;
                        }
                    }
                }
                _ => break,
            }
        }

        let location = start.join(self.current_location());

        Ok(self.node_with_span(
            AccessName {
                path: AstNodes::new(path, Some(location)),
            },
            location,
        ))
    }
}
