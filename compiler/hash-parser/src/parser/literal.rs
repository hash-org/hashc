//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_alloc::collections::row::Row;
use hash_ast::ast::*;
use hash_source::location::Location;
use hash_token::{keyword::Keyword, Token, TokenKind, TokenKindVector};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// Convert the current token (provided it is a primitive literal) into a [ExpressionKind::LiteralExpr]
    /// by simply matching on the type of the expr.
    pub(crate) fn parse_literal(&self) -> AstNode<'c, Expression<'c>> {
        let token = self.current_token();
        let literal = self.node_with_location(
            match token.kind {
                TokenKind::IntLiteral(num) => Literal::Int(IntLiteral(num)),
                TokenKind::FloatLiteral(num) => Literal::Float(FloatLiteral(num)),
                TokenKind::CharLiteral(ch) => Literal::Char(CharLiteral(ch)),
                TokenKind::StrLiteral(str) => Literal::Str(StrLiteral(str)),
                TokenKind::Keyword(Keyword::False) => Literal::Bool(BoolLiteral(false)),
                TokenKind::Keyword(Keyword::True) => Literal::Bool(BoolLiteral(true)),
                _ => unreachable!(),
            },
            token.span,
        );

        self.node_with_location(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(literal))),
            token.span,
        )
    }

    /// Parse a single map entry in a literal.
    pub(crate) fn parse_map_entry(&self) -> AstGenResult<'c, AstNode<'c, MapLiteralEntry<'c>>> {
        let start = self.current_location();

        let key = self.parse_expression_with_precedence(0)?;
        self.parse_token_atom(TokenKind::Colon)?;
        let value = self.parse_expression_with_precedence(0)?;

        Ok(self.node_with_joined_location(MapLiteralEntry { key, value }, &start))
    }

    /// Parse a map literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub(crate) fn parse_map_literal(
        &self,
        gen: Self,
        initial_entry: AstNode<'c, MapLiteralEntry<'c>>,
    ) -> AstGenResult<'c, AstNode<'c, Literal<'c>>> {
        let start = gen.current_location();
        let mut elements = gen.parse_separated_fn(
            || gen.parse_map_entry(),
            || gen.parse_token_atom(TokenKind::Comma),
        )?;

        elements.nodes.insert(0, initial_entry, &self.wall);

        Ok(self.node_with_joined_location(Literal::Map(MapLiteral { elements }), &start))
    }

    /// Parse a set literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub(crate) fn parse_set_literal(
        &self,
        gen: Self,
        initial_entry: AstNode<'c, Expression<'c>>,
    ) -> AstGenResult<'c, AstNode<'c, Literal<'c>>> {
        let start = self.current_location();

        let mut elements = gen.parse_separated_fn(
            || gen.parse_expression_with_precedence(0),
            || gen.parse_token_atom(TokenKind::Comma),
        )?;

        // insert the first item into elements
        elements.nodes.insert(0, initial_entry, &self.wall);

        Ok(self.node_with_joined_location(Literal::Set(SetLiteral { elements }), &start))
    }

    /// Function to parse a tuple literal entry with a name.
    pub(crate) fn parse_tuple_literal_entry(
        &self,
    ) -> AstGenResult<'c, AstNode<'c, TupleLiteralEntry<'c>>> {
        let start = self.current_location();
        let offset = self.offset();

        // Determine if this might have a tuple field name and optional type
        let entry = if let Some(name) = self.peek_resultant_fn(|| self.parse_name()) {
            // Here we can identify if we need to backtrack and just parse an expression...
            if !matches!(
                self.peek(),
                Some(Token {
                    kind: TokenKind::Colon | TokenKind::Eq,
                    ..
                })
            ) {
                self.offset.set(offset);
                None
            } else {
                // Try and parse an optional type...
                let ty = match self.peek() {
                    Some(token) if token.has_kind(TokenKind::Colon) => {
                        self.skip_token();

                        match self.peek() {
                            Some(token) if token.has_kind(TokenKind::Eq) => None,
                            _ => Some(self.parse_type()?),
                        }
                    }
                    _ => None,
                };

                self.parse_token_atom(TokenKind::Eq)?;

                // Now we try and parse an expression that allows re-assignment operators...
                Some(self.node_with_joined_location(
                    TupleLiteralEntry {
                        name: Some(name),
                        ty,
                        value: self.try_parse_expression_with_re_assignment()?.0,
                    },
                    &start,
                ))
            }
        } else {
            None
        };

        match entry {
            Some(entry) => Ok(entry),
            None => Ok(self.node_with_joined_location(
                TupleLiteralEntry {
                    name: None,
                    ty: None,
                    value: self.try_parse_expression_with_re_assignment()?.0,
                },
                &start,
            )),
        }
    }

    /// Parse an array literal.
    pub(crate) fn parse_array_literal(
        &self,
        tree: &'stream Row<'stream, Token>,
        span: &Location,
    ) -> AstGenResult<'c, AstNode<'c, Expression<'c>>> {
        let gen = self.from_stream(tree, *span);
        let start = gen.current_location();

        let mut elements = AstNodes::empty();

        while gen.has_token() {
            let expr = gen.parse_expression_with_precedence(0)?;
            elements.nodes.push(expr, &self.wall);

            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    gen.skip_token();
                }
                Some(token) => {
                    // if we haven't exhausted the whole token stream, then report this as a unexpected
                    // token error
                    return gen.error(
                        AstGenErrorKind::Expected,
                        Some(TokenKindVector::singleton(&self.wall, TokenKind::Comma)),
                        Some(token.kind),
                    );
                }
                None => break,
            }
        }

        Ok(gen.node_with_joined_location(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                gen.node_with_joined_location(Literal::List(ListLiteral { elements }), &start),
            ))),
            &start,
        ))
    }
}
