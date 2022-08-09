//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::location::Span;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};
use num_bigint::{BigInt, Sign};

use super::AstGen;
use crate::diagnostics::error::{ParseErrorKind, ParseResult};

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

    ///
    pub(crate) fn parse_primitive_lit(&self) -> ParseResult<AstNode<Lit>> {
        let token = self
            .next_token()
            .ok_or_else(|| self.make_error(ParseErrorKind::Eof, None, None, None))?;

        // Deal with the numeric prefix `+` by just simply ignoring it
        let lit = match token.kind {
            kind if kind.is_numeric_prefix() => {
                let is_negated = self.parse_token_fast(TokenKind::Minus).is_some();

                // We want to skip the `+` sign if it's not `-`
                if !is_negated {
                    self.skip_token();
                }

                match self.peek() {
                    Some(token) if token.kind.is_numeric() => {
                        self.skip_token();
                        return Ok(self.create_numeric_lit(is_negated));
                    }
                    token => self.error_with_location(
                        ParseErrorKind::ExpectedLiteral,
                        None,
                        token.map(|t| t.kind),
                        self.next_location(),
                    ),
                }
            }
            TokenKind::IntLit(value) => {
                Ok(Lit::Int(IntLit { value: value.into(), kind: IntLitKind::Unsuffixed }))
            }
            TokenKind::FloatLit(value) => {
                Ok(Lit::Float(FloatLit { value, kind: FloatLitKind::Unsuffixed }))
            }
            TokenKind::CharLit(value) => Ok(Lit::Char(CharLit(value))),
            TokenKind::StrLit(value) => Ok(Lit::Str(StrLit(value))),
            kind => self.error_with_location(
                ParseErrorKind::ExpectedLiteral,
                None,
                Some(kind),
                token.span,
            ),
        }?;

        Ok(self.node_with_joined_span(lit, token.span))
    }

    /// Create a numeric literal that can also be negated, it is verified
    /// that the current token is a numeric literal
    pub(crate) fn create_numeric_lit(&self, is_negated: bool) -> AstNode<Lit> {
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
    pub(crate) fn parse_map_entry(&mut self) -> ParseResult<AstNode<MapLitEntry>> {
        let start = self.current_location();

        let key = self.parse_expr_with_precedence(0)?;
        self.parse_token(TokenKind::Colon)?;
        let value = self.parse_expr_with_precedence(0)?;

        Ok(self.node_with_joined_span(MapLitEntry { key, value }, start))
    }

    /// Parse a map literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub(crate) fn parse_map_lit(&self) -> ParseResult<AstNode<Lit>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Map)));

        let start = self.current_location();
        let mut gen = self.parse_delim_tree(Delimiter::Brace, None)?;

        let elements =
            gen.parse_separated_fn(|g| g.parse_map_entry(), |g| g.parse_token(TokenKind::Comma))?;

        Ok(self.node_with_joined_span(Lit::Map(MapLit { elements }), start))
    }

    /// Parse a set literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub(crate) fn parse_set_lit(&self) -> ParseResult<AstNode<Lit>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Set)));

        let start = self.current_location();
        let mut gen = self.parse_delim_tree(Delimiter::Brace, None)?;

        let elements = gen.parse_separated_fn(
            |g| g.parse_expr_with_precedence(0),
            |g| g.parse_token(TokenKind::Comma),
        )?;

        Ok(self.node_with_joined_span(Lit::Set(SetLit { elements }), start))
    }

    /// Function to parse a tuple literal entry with a name.
    pub(crate) fn parse_tuple_lit_entry(&mut self) -> ParseResult<AstNode<TupleLitEntry>> {
        let start = self.next_location();
        let offset = self.offset();

        // Determine if this might have a tuple field name and optional type
        let entry = if let Some(name) = self.peek_resultant_fn(|g| g.parse_name()) {
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
                        ParseErrorKind::ExpectedValueAfterTyAnnotation,
                        Some(TokenKindVector::singleton(TokenKind::Eq)),
                        None,
                        Some(self.next_location()),
                    )
                })?;

                let value = self.parse_expr_with_re_assignment()?.0;

                // Now we try and parse an expression that allows re-assignment operators...
                Some(
                    self.node_with_joined_span(
                        TupleLitEntry { name: Some(name), ty, value },
                        start,
                    ),
                )
            }
        } else {
            None
        };

        match entry {
            Some(entry) => Ok(entry),
            None => {
                let value = self.parse_expr_with_re_assignment()?.0;

                Ok(self.node_with_joined_span(TupleLitEntry { name: None, ty: None, value }, start))
            }
        }
    }

    /// Parse an list literal from a given token tree.
    pub(crate) fn parse_list_lit(
        &self,
        tree: &'stream [Token],
        span: Span,
    ) -> ParseResult<AstNode<Expr>> {
        let mut gen = self.from_stream(tree, span);
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
                        ParseErrorKind::Expected,
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
