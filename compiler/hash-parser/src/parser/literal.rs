//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::location::Span;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Convert the current token (provided it is a primitive literal) into a
    /// [ExpressionKind::LiteralExpr] by simply matching on the type of the
    /// expr.
    pub(crate) fn parse_literal(&self) -> AstNode<Expression> {
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
    pub(crate) fn parse_map_entry(&self) -> AstGenResult<AstNode<MapLiteralEntry>> {
        let start = self.current_location();

        let key = self.parse_expression_with_precedence(0)?;
        self.parse_token(TokenKind::Colon)?;
        let value = self.parse_expression_with_precedence(0)?;

        Ok(self.node_with_joined_span(MapLiteralEntry { key, value }, &start))
    }

    /// Parse a map literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub(crate) fn parse_map_literal(&self) -> AstGenResult<AstNode<Literal>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Map)));

        let start = self.current_location();
        let gen = self.parse_delim_tree(Delimiter::Brace, None)?;

        let elements =
            gen.parse_separated_fn(|| gen.parse_map_entry(), || gen.parse_token(TokenKind::Comma))?;

        Ok(self.node_with_joined_span(Literal::Map(MapLiteral { elements }), &start))
    }

    /// Parse a set literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub(crate) fn parse_set_literal(&self) -> AstGenResult<AstNode<Literal>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Set)));

        let start = self.current_location();
        let gen = self.parse_delim_tree(Delimiter::Brace, None)?;

        let elements = gen.parse_separated_fn(
            || gen.parse_expression_with_precedence(0),
            || gen.parse_token(TokenKind::Comma),
        )?;

        Ok(self.node_with_joined_span(Literal::Set(SetLiteral { elements }), &start))
    }

    /// Function to parse a tuple literal entry with a name.
    pub(crate) fn parse_tuple_literal_entry(&self) -> AstGenResult<AstNode<TupleLiteralEntry>> {
        let start = self.next_location();
        let offset = self.offset();

        // Determine if this might have a tuple field name and optional type
        let entry = if let Some(name) = self.peek_resultant_fn(|| self.parse_name()) {
            // Here we can identify if we need to backtrack and just parse an expression...
            if !matches!(self.peek(), Some(Token { kind: TokenKind::Colon | TokenKind::Eq, .. })) {
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

                self.parse_token_fast(TokenKind::Eq).ok_or_else(|| {
                    self.make_error(
                        AstGenErrorKind::ExpectedValueAfterTyAnnotation,
                        Some(TokenKindVector::singleton(TokenKind::Eq)),
                        None,
                        Some(self.next_location()),
                    )
                })?;

                // Now we try and parse an expression that allows re-assignment operators...
                Some(self.node_with_joined_span(
                    TupleLiteralEntry {
                        name: Some(name),
                        ty,
                        value: self.parse_expression_with_re_assignment()?.0,
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
                    value: self.parse_expression_with_re_assignment()?.0,
                },
                &start,
            )),
        }
    }

    /// Parse an list literal from a given token tree.
    pub(crate) fn parse_list_literal(
        &self,
        tree: &'stream [Token],
        span: Span,
    ) -> AstGenResult<AstNode<Expression>> {
        let gen = self.from_stream(tree, span);

        let mut elements = AstNodes::empty();

        while gen.has_token() {
            let expr = gen.parse_expression_with_precedence(0)?;
            elements.nodes.push(expr);

            match gen.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    gen.skip_token();
                }
                Some(token) => {
                    // if we haven't exhausted the whole token stream, then report this as a
                    // unexpected token error
                    return gen.error(
                        AstGenErrorKind::Expected,
                        Some(TokenKindVector::singleton(TokenKind::Comma)),
                        Some(token.kind),
                    );
                }
                None => break,
            }
        }

        Ok(gen.node_with_span(
            Expression::new(ExpressionKind::LiteralExpr(LiteralExpr(
                gen.node_with_span(Literal::List(ListLiteral { elements }), span),
            ))),
            span,
        ))
    }
}
