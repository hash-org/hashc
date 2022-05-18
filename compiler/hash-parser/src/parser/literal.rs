//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_alloc::{collections::row::Row, row};
use hash_ast::ast::*;
use hash_source::location::Location;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// Convert the current token (provided it is a primitive literal) into a [ExpressionKind::LiteralExpr]
    /// by simply matching on the type of the expr.
    pub(crate) fn parse_literal(&self) -> AstNode<'c, Expression<'c>> {
        let token = self.current_token();
        let literal = self.node_with_span(
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

        self.node_with_span(
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

        Ok(self.node_with_joined_span(MapLiteralEntry { key, value }, &start))
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

        Ok(self.node_with_joined_span(Literal::Map(MapLiteral { elements }), &start))
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

        Ok(self.node_with_joined_span(Literal::Set(SetLiteral { elements }), &start))
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
                Some(self.node_with_joined_span(
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
            None => Ok(self.node_with_joined_span(
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

        Ok(gen.node_with_joined_span(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                gen.node_with_joined_span(Literal::List(ListLiteral { elements }), &start),
            ))),
            &start,
        ))
    }

    /// Parse a [StructLiteral] and turn it into an [Expression].
    ///
    ///
    /// ### De-sugaring process for [StructLiteral] entries
    ///
    /// we want to support the syntax where we can just assign a struct field that has
    /// the same name as a variable in scope. For example, if you were to create a
    /// struct like so:
    ///
    /// ```text
    /// name := "Viktor";
    /// dog  := Dog { name };
    /// ```
    /// This should be de-sugared into:
    /// ```text
    /// dog := Dog { name = name };
    /// ```
    ///
    pub fn parse_struct_literal(
        &self,
        name: AstNode<'c, AccessName<'c>>,
        type_args: AstNodes<'c, Type<'c>>,
        tree: &'stream Row<'stream, Token>,
    ) -> AstGenResult<'c, AstNode<'c, Literal<'c>>> {
        let start = self.current_location();
        let gen = self.from_stream(tree, start);

        let mut entries = AstNodes::empty();

        while gen.has_token() {
            let name = gen.parse_name()?;
            let location = name.location();

            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Eq) => {
                    gen.skip_token();

                    let value = gen.parse_expression_with_precedence(0)?;

                    entries.nodes.push(
                        gen.node_with_span(
                            StructLiteralEntry { name, value },
                            location.join(gen.current_location()),
                        ),
                        &self.wall,
                    );

                    // now we eat the next token, checking that it is a comma
                    match gen.peek() {
                            Some(token) if token.has_kind(TokenKind::Comma) => gen.skip_token(),
                            Some(token) => gen.error_with_location(
                                AstGenErrorKind::Expected,
                                Some(TokenKindVector::from_row(
                                    row![&self.wall; TokenKind::Comma, TokenKind::Delimiter(Delimiter::Brace, false)],
                                )),
                                Some(token.kind),
                                token.span,
                            )?,
                            None => break,
                        };
                }
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    gen.skip_token();

                    // we need to copy the name node and make it into a new expression with the same span
                    let name_copy = gen.make_variable_from_identifier(name.ident, name.location());

                    entries.nodes.push(
                        gen.node_with_span(
                            StructLiteralEntry {
                                name,
                                value: name_copy,
                            },
                            location.join(gen.current_location()),
                        ),
                        &self.wall,
                    );
                }
                None => {
                    // we need to copy the name node and make it into a new expression with the same span
                    let name_copy = gen.make_variable_from_identifier(name.ident, name.location());

                    entries.nodes.push(
                        gen.node_with_span(
                            StructLiteralEntry {
                                name,
                                value: name_copy,
                            },
                            location.join(gen.current_location()),
                        ),
                        &self.wall,
                    );

                    break;
                }
                Some(token) => gen.error_with_location(
                    AstGenErrorKind::Expected,
                    Some(TokenKindVector::from_row(row![&self.wall; TokenKind::Eq,
                            TokenKind::Comma,
                            TokenKind::Delimiter(Delimiter::Brace, false)])),
                    Some(token.kind),
                    token.span,
                )?,
            }
        }

        Ok(self.node_with_joined_span(
            Literal::Struct(StructLiteral {
                name,
                type_args,
                entries,
            }),
            &start,
        ))
    }
}
