//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::{identifier::Identifier, location::ByteRange};
use hash_token::{delimiter::Delimiter, keyword::Keyword, FloatLitKind, IntLitKind, TokenKind};

use super::AstGen;
use crate::diagnostics::{
    error::{ParseErrorKind, ParseResult},
    expected::ExpectedItem,
};

impl<'s> AstGen<'s> {
    /// Parse a primitive literal, which means it can be either a `char`,
    /// `integer`, `float` or a `string`.
    pub(crate) fn parse_primitive_lit(&mut self) -> ParseResult<AstNode<Lit>> {
        let token = self.current_token();

        Ok(self.node_with_span(
            match token.kind {
                TokenKind::Int(_, _) | TokenKind::Float(_) => return self.parse_numeric_lit(),
                TokenKind::Char(value) => Lit::Char(CharLit { data: value }),
                TokenKind::Str(value) => Lit::Str(StrLit { data: value }),
                TokenKind::Keyword(Keyword::False) => Lit::Bool(BoolLit { data: false }),
                TokenKind::Keyword(Keyword::True) => Lit::Bool(BoolLit { data: true }),
                _ => self.err_with_location(
                    ParseErrorKind::ExpectedLit,
                    ExpectedItem::empty(),
                    Some(token.kind),
                    token.span,
                )?,
            },
            token.span,
        ))
    }

    /// Function to parse a primitive numeric lit with the option of negating
    /// the value immediately.
    pub(crate) fn parse_numeric_lit(&mut self) -> ParseResult<AstNode<Lit>> {
        let token = self.current_token();

        let lit = match token.kind {
            TokenKind::Int(base, kind) => {
                // don't include the length of the prefix in the span
                let span = if let IntLitKind::Suffixed(suffix) = kind {
                    ByteRange::new(
                        token.span.start(),
                        token.span.end() - Identifier::from(suffix).len(),
                    )
                } else {
                    token.span
                };

                let hunk = Hunk::create(self.make_span(span));
                Lit::Int(IntLit { hunk, base, kind })
            }
            TokenKind::Float(kind) => {
                let span = if let FloatLitKind::Suffixed(suffix) = kind {
                    ByteRange::new(
                        token.span.start(),
                        token.span.end() - Identifier::from(suffix).len(),
                    )
                } else {
                    token.span
                };

                let hunk = Hunk::create(self.make_span(span));
                Lit::Float(FloatLit { hunk, kind })
            }
            _ => panic!("expected numeric token in parse_numeric_lit()"),
        };

        Ok(self.node_with_span(lit, token.span))
    }

    /// Function to parse a [TupleLitEntry] with a name or parse a parenthesised
    /// expression. In the event that the entry does not have a name `name =
    /// ...`, or a name with a associated type `name : <type> = ...`, then
    /// this will just parse the entry as a single expression rather than a
    /// tuple entry with an associated name and type.
    pub(crate) fn parse_tuple_lit_entry(&mut self) -> ParseResult<AstNode<TupleLitEntry>> {
        let start = self.next_pos();
        let offset = self.offset();

        // Determine if this might have a tuple field name and optional type
        let entry = if let Some(name) = self.peek_resultant_fn(|g| g.parse_name()) {
            // Here we can identify if we need to backtrack and just parse an expression...
            match self.peek_kind() {
                // If this is an `=`, then we need to see if there is a second `=` after it to
                // ensure that it isn't a binary expression.
                Some(TokenKind::Eq)
                    if self.peek_second().map_or(false, |t| t.has_kind(TokenKind::Eq)) =>
                {
                    self.set_pos(offset);
                    None
                }
                Some(TokenKind::Access) => {
                    self.set_pos(offset);
                    None
                }
                Some(kind) if !matches!(kind, TokenKind::Colon | TokenKind::Eq) => {
                    self.set_pos(offset);
                    None
                }
                Some(_) => {
                    // Try and parse an optional type...
                    let ty = match self.peek_kind() {
                        Some(TokenKind::Colon) => {
                            self.skip_fast(); // ':'

                            match self.peek_kind() {
                                Some(TokenKind::Eq) => None,
                                _ => Some(self.parse_ty()?),
                            }
                        }
                        _ => None,
                    };

                    self.parse_token_fast(TokenKind::Eq).ok_or_else(|| {
                        self.make_err(
                            ParseErrorKind::ExpectedValueAfterTyAnnotation,
                            ExpectedItem::Eq,
                            None,
                            Some(self.next_pos()),
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
                    self.set_pos(offset);
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

    /// Parse an array literal from a bracket token tree.
    pub(crate) fn parse_array_lit(&mut self) -> ParseResult<AstNode<Expr>> {
        self.in_tree(Delimiter::Bracket, None, |gen| {
            let elements = gen.parse_nodes(
                |g| g.parse_expr_with_precedence(0),
                |g| g.parse_token(TokenKind::Comma),
            );

            let span = gen.range();
            let data = gen.node_with_span(Lit::Array(ArrayLit { elements }), span);
            Ok(gen.node_with_span(Expr::Lit(LitExpr { data }), span))
        })
    }
}
