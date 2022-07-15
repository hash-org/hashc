//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::identifier::Identifier;
use hash_token::{Token, TokenKind};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a singular [Name] from the current token stream.
    pub fn parse_name(&self) -> AstGenResult<AstNode<Name>> {
        match self.next_token() {
            Some(Token { kind: TokenKind::Ident(ident), span }) => {
                Ok(self.node_with_span(Name { ident: *ident }, *span))
            }
            _ => self.error(AstGenErrorKind::ExpectedIdentifier, None, None),
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

    /// This function follows a similar process as parsing a [Namespace],
    /// however it parses the namespace and turns it into a
    /// [ExprKind::Access] which specifies how the members are
    /// accessed.
    pub(crate) fn parse_ns_access(
        &self,
        name: Option<AstNode<Name>>,
    ) -> AstGenResult<AstNode<Expr>> {
        let name = match name {
            Some(name) => name,
            None => self.parse_name()?,
        };

        // Collect the path into a vector of names as it is easier to create
        // the `Access` expr from a list rather than continuing to recurse.
        let mut path = vec![name];

        loop {
            match (self.peek(), self.peek_second()) {
                (Some(tok), Some(second_tok))
                    if tok.has_kind(TokenKind::Colon) && second_tok.has_kind(TokenKind::Colon) =>
                {
                    self.offset.update(|current| current + 2); // '::'
                    path.push(self.parse_name()?);
                }
                _ => break,
            }
        }

        let mut path_iter = path.into_iter();

        // We just need to put this one one the name
        let name = path_iter.next().unwrap();
        let name_span = name.span();

        // The base case of the `access` is just a variable expression
        let mut lhs =
            self.node_with_span(Expr::new(ExprKind::Variable(VariableExpr { name })), name_span);

        // Iterate backwards and build up each part of the access backwards
        for node in path_iter {
            let span = lhs.span().join(node.span());

            lhs = self.node_with_joined_span(
                Expr::new(ExprKind::Access(AccessExpr {
                    subject: lhs,
                    property: node,
                    kind: AccessKind::Namespace,
                })),
                &span,
            );
        }

        Ok(lhs)
    }
}
