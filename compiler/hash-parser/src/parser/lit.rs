//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::location::Span;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};
use num_bigint::{BigInt, Sign};

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Convert the current token (provided it is a primitive literal) into a
    /// [ExprKind::LitExpr] by simply matching on the type of the
    /// expr.
    pub(crate) fn parse_atomic_lit(&self) -> AstNode<Lit> {
        let token = self.current_token();

        self.node_with_span(
            match token.kind {
                // @@Todo: support Integer/Float ascriptions
                TokenKind::IntLit(value) => {
                    Lit::Int(IntLit { value: value.into(), kind: IntLitKind::Unsuffixed })
                }
                TokenKind::FloatLit(value) => {
                    Lit::Float(FloatLit { value, kind: FloatLitKind::Unsuffixed })
                }
                TokenKind::CharLit(value) => Lit::Char(CharLit(value)),
                TokenKind::StrLit(value) => Lit::Str(StrLit(value)),
                TokenKind::Keyword(Keyword::False) => Lit::Bool(BoolLit(false)),
                TokenKind::Keyword(Keyword::True) => Lit::Bool(BoolLit(true)),
                _ => unreachable!(),
            },
            token.span,
        )
    }

    /// Parse a numeric literal that can also be negated
    pub(crate) fn parse_numeric_lit(&self, is_negated: bool) -> AstNode<Lit> {
        let token = self.current_token();

        self.node_with_span(
            match token.kind {
                // @@Todo: support Integer/Float ascriptions
                TokenKind::IntLit(value) => {
                    let value = BigInt::from_bytes_be(
                        if is_negated { Sign::Minus } else { Sign::NoSign },
                        &value.to_be_bytes(),
                    );

                    Lit::Int(IntLit { value, kind: IntLitKind::Unsuffixed })
                }
                TokenKind::FloatLit(value) => {
                    let value = if is_negated { -value } else { value };

                    Lit::Float(FloatLit { value, kind: FloatLitKind::Unsuffixed })
                }
                _ => unreachable!(),
            },
            token.span,
        )
    }

    /// Parse a single map entry in a literal.
    pub(crate) fn parse_map_entry(&self) -> AstGenResult<AstNode<MapLitEntry>> {
        let start = self.current_location();

        let key = self.parse_expr_with_precedence(0)?;
        self.parse_token(TokenKind::Colon)?;
        let value = self.parse_expr_with_precedence(0)?;

        Ok(self.node_with_joined_span(MapLitEntry { key, value }, &start))
    }

    /// Parse a map literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub(crate) fn parse_map_lit(&self) -> AstGenResult<AstNode<Lit>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Map)));

        let start = self.current_location();
        let gen = self.parse_delim_tree(Delimiter::Brace, None)?;

        let elements =
            gen.parse_separated_fn(|| gen.parse_map_entry(), || gen.parse_token(TokenKind::Comma))?;

        Ok(self.node_with_joined_span(Lit::Map(MapLit { elements }), &start))
    }

    /// Parse a set literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub(crate) fn parse_set_lit(&self) -> AstGenResult<AstNode<Lit>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Set)));

        let start = self.current_location();
        let gen = self.parse_delim_tree(Delimiter::Brace, None)?;

        let elements = gen.parse_separated_fn(
            || gen.parse_expr_with_precedence(0),
            || gen.parse_token(TokenKind::Comma),
        )?;

        Ok(self.node_with_joined_span(Lit::Set(SetLit { elements }), &start))
    }

    /// Function to parse a tuple literal entry with a name.
    pub(crate) fn parse_tuple_lit_entry(&self) -> AstGenResult<AstNode<TupleLitEntry>> {
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
                    TupleLitEntry {
                        name: Some(name),
                        ty,
                        value: self.parse_expr_with_re_assignment()?.0,
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
                TupleLitEntry {
                    name: None,
                    ty: None,
                    value: self.parse_expr_with_re_assignment()?.0,
                },
                &start,
            )),
        }
    }

    /// Parse an list literal from a given token tree.
    pub(crate) fn parse_list_lit(
        &self,
        tree: &'stream [Token],
        span: Span,
    ) -> AstGenResult<AstNode<Expr>> {
        let gen = self.from_stream(tree, span);

        let mut elements = AstNodes::empty();

        while gen.has_token() {
            let expr = gen.parse_expr_with_precedence(0)?;
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
            Expr::new(ExprKind::LitExpr(LitExpr(
                gen.node_with_span(Lit::List(ListLit { elements }), span),
            ))),
            span,
        ))
    }
}
