//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::{constant::CONSTANT_MAP, location::Span};
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use super::AstGen;
use crate::diagnostics::error::{ParseErrorKind, ParseResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a primitive literal, which means it can be either a `char`,
    /// `integer`, `float` or a `string`.
    pub(crate) fn parse_primitive_lit(&self) -> ParseResult<AstNode<Lit>> {
        let token = self.current_token();

        Ok(self.node_with_span(
            match token.kind {
                TokenKind::IntLit(_) | TokenKind::FloatLit(_) => {
                    return self.parse_numeric_lit(false)
                }
                TokenKind::CharLit(value) => Lit::Char(CharLit { data: value }),
                TokenKind::StrLit(value) => Lit::Str(StrLit { data: value }),
                TokenKind::Keyword(Keyword::False) => Lit::Bool(BoolLit { data: false }),
                TokenKind::Keyword(Keyword::True) => Lit::Bool(BoolLit { data: true }),

                _ => self.err_with_location(
                    ParseErrorKind::ExpectedLit,
                    None,
                    Some(token.kind),
                    token.span,
                )?,
            },
            token.span,
        ))
    }

    /// Function to parse a primitive numeric lit with the option of negating
    /// the value immediately.
    pub(crate) fn parse_numeric_lit(&self, negate: bool) -> ParseResult<AstNode<Lit>> {
        let token = self.current_token();

        Ok(self.node_with_span(
            match token.kind {
                TokenKind::IntLit(value) => {
                    // If it is specified that we should negate this constant, then we modify the
                    // literal that is stored within the constant map with the modified value.
                    if negate {
                        CONSTANT_MAP.negate_int_constant(value);
                    }

                    let (ty, suffix) =
                        CONSTANT_MAP.map_int_constant(value, |val| (val.ty, val.suffix));

                    // Despite the fact that we always know the type, we still want to preserve
                    // information about whether this constant had a specified
                    // suffix, this is used to accurately reflect the parsed AST
                    // for purposes like pretty printing the suffix, or disallowing suffixes
                    // in particular situations.
                    if suffix.is_some() {
                        Lit::Int(IntLit { value, kind: IntLitKind::Suffixed(ty) })
                    } else {
                        Lit::Int(IntLit { value, kind: IntLitKind::Unsuffixed })
                    }
                }
                TokenKind::FloatLit(value) => {
                    // If it is specified that we should negate this constant, then we modify the
                    // literal that is stored within the constant map with the modified value.
                    if negate {
                        CONSTANT_MAP.negate_float_constant(value);
                    }

                    let (ty, suffix) =
                        CONSTANT_MAP.map_float_constant(value, |val| (val.ty, val.suffix));

                    if suffix.is_some() {
                        Lit::Float(FloatLit { value, kind: FloatLitKind::Suffixed(ty) })
                    } else {
                        Lit::Float(FloatLit { value, kind: FloatLitKind::Unsuffixed })
                    }
                }
                _ => panic!("expected numeric token in parse_numeric_lit()"),
            },
            token.span,
        ))
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
    pub(crate) fn parse_map_lit(&mut self) -> ParseResult<AstNode<Lit>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Map)));

        let start = self.current_location();
        let mut gen = self.parse_delim_tree(Delimiter::Brace, None)?;

        let elements =
            gen.parse_separated_fn(|g| g.parse_map_entry(), |g| g.parse_token(TokenKind::Comma));
        self.consume_gen(gen);

        Ok(self.node_with_joined_span(Lit::Map(MapLit { elements }), start))
    }

    /// Parse a set literal which is made of braces with an arbitrary number of
    /// fields separated by commas.
    pub(crate) fn parse_set_lit(&mut self) -> ParseResult<AstNode<Lit>> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Set)));

        let start = self.current_location();
        let mut gen = self.parse_delim_tree(Delimiter::Brace, None)?;

        let elements = gen.parse_separated_fn(
            |g| g.parse_expr_with_precedence(0),
            |g| g.parse_token(TokenKind::Comma),
        );
        self.consume_gen(gen);

        Ok(self.node_with_joined_span(Lit::Set(SetLit { elements }), start))
    }

    /// Function to parse a [TupleLitEntry] with a name or parse a parenthesised
    /// expression. In the event that the entry does not have a name `name =
    /// ...`, or a name with a associated type `name : <type> = ...`, then
    /// this will just parse the entry as a single expression rather than a
    /// tuple entry with an associated name and type.
    pub(crate) fn parse_tuple_lit_entry(&mut self) -> ParseResult<AstNode<TupleLitEntry>> {
        let start = self.next_location();
        let offset = self.offset();

        // Determine if this might have a tuple field name and optional type
        let entry = if let Some(name) = self.peek_resultant_fn(|g| g.parse_name()) {
            // Here we can identify if we need to backtrack and just parse an expression...
            match self.peek() {
                // If this is an `=`, then we need to see if there is a second `=` after it to
                // ensure that it isn't a binary expression.
                Some(Token { kind: TokenKind::Eq, .. })
                    if self.peek_second().map_or(false, |t| t.has_kind(TokenKind::Eq)) =>
                {
                    self.offset.set(offset);
                    None
                }
                Some(Token { kind, .. }) if !matches!(kind, TokenKind::Colon | TokenKind::Eq) => {
                    self.offset.set(offset);
                    None
                }
                Some(_) => {
                    // Try and parse an optional type...
                    let ty = match self.peek() {
                        Some(token) if token.has_kind(TokenKind::Colon) => {
                            self.skip_token();

                            match self.peek() {
                                Some(token) if token.has_kind(TokenKind::Eq) => None,
                                _ => Some(self.parse_ty()?),
                            }
                        }
                        _ => None,
                    };

                    self.parse_token_fast(TokenKind::Eq).ok_or_else(|| {
                        self.make_err(
                            ParseErrorKind::ExpectedValueAfterTyAnnotation,
                            Some(TokenKindVector::singleton(TokenKind::Eq)),
                            None,
                            Some(self.next_location()),
                        )
                    })?;

                    let value = self.parse_expr_with_re_assignment()?.0;

                    // Now we try and parse an expression that allows re-assignment operators...
                    Some(self.node_with_joined_span(
                        TupleLitEntry { name: Some(name), ty, value },
                        start,
                    ))
                }
                None => {
                    self.offset.set(offset);
                    None
                }
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
                    return gen.err(
                        ParseErrorKind::Expected,
                        Some(TokenKindVector::singleton(TokenKind::Comma)),
                        Some(token.kind),
                    );
                }
                None => break,
            }
        }

        Ok(gen.node_with_span(
            Expr::Lit(LitExpr { data: gen.node_with_span(Lit::List(ListLit { elements }), span) }),
            span,
        ))
    }
}
