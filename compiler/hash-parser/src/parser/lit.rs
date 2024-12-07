//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::{identifier::Identifier, location::ByteRange};
use hash_token::{delimiter::Delimiter, keyword::Keyword, FloatLitKind, IntLitKind, TokenKind};
use hash_utils::thin_vec::thin_vec;

use super::AstGen;
use crate::diagnostics::error::ParseResult;

impl AstGen<'_> {
    /// Parse a primitive literal, which means it can be either a `char`,
    /// `integer`, `float` or a `string`.
    pub(crate) fn parse_primitive_lit(&mut self) -> AstNode<Lit> {
        let token = self.current_token();
        debug_assert!(token.kind.is_lit());

        // `parse_numeric_literal()` will skip itself.
        if !token.kind.is_numeric() {
            self.skip_fast(token.kind);
        }

        self.node_with_span(
            match token.kind {
                TokenKind::Int(_, _) | TokenKind::Byte(_) | TokenKind::Float(_) => {
                    return self.parse_numeric_lit()
                }
                TokenKind::Char(value) => Lit::Char(CharLit { data: value }),
                TokenKind::Str(value) => Lit::Str(StrLit { data: value }),
                TokenKind::Keyword(Keyword::False) => Lit::Bool(BoolLit { data: false }),
                TokenKind::Keyword(Keyword::True) => Lit::Bool(BoolLit { data: true }),
                _ => unreachable!(),
            },
            token.span,
        )
    }

    /// Function to parse a primitive numeric lit with the option of negating
    /// the value immediately.
    pub(crate) fn parse_numeric_lit(&mut self) -> AstNode<Lit> {
        let token = self.current_token();
        debug_assert!(token.kind.is_numeric());
        self.skip_fast(token.kind); // `float` or `int`

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
            TokenKind::Byte(value) => Lit::Byte(ByteLit { data: value }),
            _ => panic!("expected numeric token in parse_numeric_lit()"),
        };

        self.node_with_span(lit, token.span)
    }

    /// Function to parse a tuple element, which is represented as an [ExprArg].
    pub(crate) fn parse_tuple_arg(&mut self) -> ParseResult<AstNode<ExprArg>> {
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;

        let start = self.current_pos();
        let offset = self.position();

        if let Some(name) = self.peek_resultant_fn(|g| g.parse_name()) {
            // If the next item isn't a `=`, i.e. an assignment to a name, then
            // we just parse this as an expression.
            if self.peek_kind() != Some(TokenKind::Eq) {
                self.set_pos(offset);
            } else {
                self.skip_fast(TokenKind::Eq);

                // peek next to check if it is a `==`, @@Todo: perhaps we should
                // introduce an `EqEq` token?
                if self.peek_kind() == Some(TokenKind::Eq) {
                    self.set_pos(offset); // backtrack...
                } else {
                    let value = self.parse_expr_with_precedence(0)?;

                    // Now we try and parse an expression that allows re-assignment operators...
                    return Ok(self.node_with_joined_span(
                        ExprArg { name: Some(name), value, macros },
                        start,
                    ));
                }
            }
        }

        let value = self.parse_expr_with_re_assignment()?.0;
        Ok(self.node_with_joined_span(ExprArg { name: None, value, macros }, start))
    }

    /// Parse an array literal from a bracket token tree. This function
    /// also handles array literals that specify a repeat expression, i.e.
    /// `[0; 10]` which would be an array of 10 `0`'s.
    pub(crate) fn parse_array_lit(&mut self) -> ParseResult<AstNode<Expr>> {
        self.in_tree(Delimiter::Bracket, None, |gen| {
            macro_rules! make_arr {
                ($elements:expr; $span:expr) => {{
                    let elements = gen.nodes_with_span($elements, $span);
                    Ok(gen.node_with_span(Expr::Array(ArrayExpr { elements }), $span))
                }};
            }

            let span = gen.range();

            // If the generator is empty, then we can just return an empty array literal...
            if gen.is_empty() {
                return make_arr!(thin_vec![]; span);
            }

            // Parse the initial expression, then if the next token is a
            // semi colon, this must be a repeat expression!
            let start = gen.parse_expr_with_precedence(0)?;

            match gen.peek_kind() {
                Some(TokenKind::Semi) => {
                    gen.skip_fast(TokenKind::Semi); // ';'

                    let repeat = gen.parse_expr_with_precedence(0)?;

                    Ok(gen
                        .node_with_span(Expr::Repeat(RepeatExpr { subject: start, repeat }), span))
                }
                Some(TokenKind::Comma) => {
                    // We might have to perform some cleanup here, if the next token is a comma,
                    // then we need to parse the rest of the elements.
                    gen.skip_fast(TokenKind::Comma); // ';'

                    let mut elements = gen.parse_nodes(
                        |g| g.parse_expr_with_precedence(0),
                        |g| g.parse_token(TokenKind::Comma),
                    );

                    // Insert the first element into the array...
                    elements.insert(start, 0);
                    Ok(gen.node_with_span(Expr::Array(ArrayExpr { elements }), span))
                }
                _ => {
                    make_arr!(thin_vec![start]; span)
                }
            }
        })
    }
}
