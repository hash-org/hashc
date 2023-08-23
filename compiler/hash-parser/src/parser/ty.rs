//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_source::identifier::IDENTS;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};
use hash_utils::{smallvec::smallvec, thin_vec::thin_vec};

use super::AstGen;
use crate::diagnostics::error::{ParseErrorKind, ParseResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a [Ty]. This includes all forms of a [Ty]. This function
    /// does not deal with any kind of [Ty] annotation or [TyFnDef]
    /// syntax.
    pub(crate) fn parse_ty(&mut self) -> ParseResult<AstNode<Ty>> {
        self.parse_ty_with_precedence(0)
    }

    /// Parse a [Ty] with precedence in mind. The type notation contains
    /// [BinTyOp] operators which are binary operators for type terms. This
    /// function implements the same precedence algorithm for correctly
    /// forming binary type expressions.
    fn parse_ty_with_precedence(&mut self, min_prec: u8) -> ParseResult<AstNode<Ty>> {
        let mut lhs = self.parse_singular_ty()?;
        let lhs_span = lhs.byte_range();

        loop {
            let (op, consumed_tokens) = self.parse_ty_op();

            match op {
                Some(op) => {
                    let (l_prec, r_prec) = op.infix_binding_power();

                    // If the precedence from this operator is lower than our `min_prec` we
                    // need to backtrack...
                    if l_prec < min_prec {
                        break;
                    }

                    self.offset.update(|x| x + consumed_tokens as usize);

                    // Now recurse and get the `rhs` of the operator.
                    let rhs = self.parse_ty_with_precedence(r_prec)?;

                    // transform the operator into an `UnaryTy` or `MergeTy` based on the operator
                    lhs =
                        match op {
                            BinTyOp::Union => self
                                .node_with_joined_span(Ty::Union(UnionTy { lhs, rhs }), lhs_span),
                            BinTyOp::Merge => self
                                .node_with_joined_span(Ty::Merge(MergeTy { lhs, rhs }), lhs_span),
                        }
                }
                _ => break,
            }
        }

        Ok(lhs)
    }

    /// Parse a [Ty]. This includes only singular forms of a type.
    fn parse_singular_ty(&mut self) -> ParseResult<AstNode<Ty>> {
        let token = self.peek().ok_or_else(|| {
            self.make_err(ParseErrorKind::ExpectedType, None, None, Some(self.next_pos()))
        })?;

        let mut multi_ty_components = true;
        let span = token.span;

        // Parse the initial part of the type
        let mut ty = match &token.kind {
            TokenKind::Amp => {
                self.skip_token();

                // Check if this is a raw ref
                let kind = self
                    .parse_token_fast(TokenKind::Keyword(Keyword::Raw))
                    .map(|_| self.node_with_span(RefKind::Raw, self.current_pos()));

                // Parse a mutability modifier if any
                let mutability = self
                    .parse_token_fast(TokenKind::Keyword(Keyword::Mut))
                    .map(|_| self.node_with_span(Mutability::Mutable, self.current_pos()));

                Ty::Ref(RefTy { inner: self.parse_ty()?, kind, mutability })
            }
            TokenKind::Ident(id) => {
                self.skip_token();

                let name = self.node_with_span(Name { ident: *id }, span);
                Ty::Named(NamedTy { name })
            }

            // Expression in the type.
            TokenKind::Tree(Delimiter::Brace, tree_index) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index as usize).unwrap();
                let mut gen = self.from_stream(tree, token.span);
                let expr = gen.parse_expr_with_precedence(0)?;
                self.consume_gen(gen);

                Ty::Expr(ExprTy { expr })
            }

            // Array type
            TokenKind::Tree(Delimiter::Bracket, tree_index) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index as usize).unwrap();
                let mut gen = self.from_stream(tree, token.span);

                // @@ErrorRecovery: Investigate introducing `Err` variant into types...
                let inner_type = gen.parse_ty()?;

                // Optionally, the user may specify a size for the array type by
                // using a `;` followed by an expression that evaluates to a]
                // constant integer.
                let len = if gen.peek().map(|x| x.kind) == Some(TokenKind::Semi) {
                    gen.skip_token();
                    Some(gen.parse_expr()?)
                } else {
                    None
                };

                self.consume_gen(gen);

                Ty::Array(ArrayTy { inner: inner_type, len })
            }

            // Tuple or function type
            TokenKind::Tree(Delimiter::Paren, _) => {
                multi_ty_components = false;
                self.parse_fn_or_tuple_ty()?
            }

            // Special syntax for the never type `!`
            TokenKind::Exclamation => {
                self.skip_token();

                Ty::Named(NamedTy {
                    name: self.node_with_span(Name { ident: IDENTS.never }, token.span),
                })
            }

            // Parse a macro invocation
            TokenKind::Pound => {
                let macros = self.parse_macro_invocations(MacroKind::Ast)?.unwrap();
                let subject = self.parse_singular_ty()?;

                Ty::Macro(TyMacroInvocation { macros, subject })
            }

            // Type function, which is a collection of arguments enclosed in `<...>` and then
            // followed by a return type
            TokenKind::Lt => {
                self.skip_token();

                multi_ty_components = false;
                self.parse_ty_fn()?
            }

            // This allows for the user to use the shorthand for literal types within
            // type positions, if the token is a primitive literal, then we parse it as
            // a expression in a type.
            kind if kind.is_lit() => {
                let expr = self.parse_expr()?;
                Ty::Expr(ExprTy { expr })
            }

            kind => {
                self.err_with_location(ParseErrorKind::ExpectedType, None, Some(*kind), span)?
            }
        };

        // Deal with type function call, or type access
        while multi_ty_components && let Some(token) = self.peek() {
            ty = match token.kind {
                TokenKind::Lt => {
                    self.skip_token();

                    Ty::TyFnCall(TyFnCall {
                        subject: self.node_with_joined_span(
                            Expr::Ty(TyExpr { ty: self.node_with_joined_span(ty, span) }),
                            span,
                        ),
                        args: self.parse_ty_args(true)?,
                    })
                }
                // Function syntax which allow to express `U -> T` whilst implying `(U -> T)`
                TokenKind::Minus if matches!(self.peek_second(), Some(token) if token.has_kind(TokenKind::Gt)) => {
                    self.offset.update(|offset| offset + 2);
                    let return_ty = self.parse_ty()?;

                    let ty_arg = self.node_with_span(TyArg {
                        name: None,
                        ty: self.node_with_joined_span(ty, span),
                        // @@Note: this will always be none since the above function
                        // will parse the args and then apply it to us as the subject.
                        // 
                        // So if `#foo U -> T` is present, we parse as `TyMacroInvocation { subject: U -> T, macros: #foo }`
                        macros: None
                    }, span);

                    Ty::Fn(FnTy {
                        params: self.nodes_with_span(thin_vec![ty_arg], span),
                        return_ty,
                    })
                }

                TokenKind::Colon if matches!(self.peek_second(), Some(token) if token.has_kind(TokenKind::Colon)) => {
                    self.offset.update(|offset| offset + 2);

                    Ty::Access(AccessTy {
                        subject: self.node_with_joined_span(ty, span),
                        property: self.parse_name()?
                    })
                }
                _ => break
            }
        }

        Ok(self.node_with_joined_span(ty, span))
    }

    /// This parses type arguments, however due to the nature of the language
    /// grammar, since the [TokenKind] could be a [`TokenKind::Lt`] or `<`, it
    /// could also be a comparison rather than the beginning of a type argument.
    /// Therefore, we have to lookahead to see if there is   type followed
    /// by either a comma (which locks the closing [`TokenKind::Gt`].
    pub(crate) fn parse_ty_args(&mut self, lt_eaten: bool) -> ParseResult<AstNodes<TyArg>> {
        // Only parse is if the caller specifies that they haven't eaten an `lt`
        if !lt_eaten {
            self.parse_token(TokenKind::Lt)?;
        }

        let start = self.current_pos();
        let mut ty_args = thin_vec![];

        loop {
            ty_args.push(self.parse_ty_arg()?);

            // Now consider if the bound is closing or continuing with a comma...
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    self.skip_token();
                }
                Some(token) if token.has_kind(TokenKind::Gt) => {
                    self.skip_token();
                    break;
                }
                Some(token) => self.err(
                    ParseErrorKind::UnExpected,
                    Some(TokenKindVector::from_vec(smallvec![TokenKind::Comma, TokenKind::Gt])),
                    Some(token.kind),
                )?,
                None => self.unexpected_eof()?,
            }
        }

        // Update the location of the type bound to reflect the '<' and '>' tokens...
        Ok(self.nodes_with_joined_span(ty_args, start))
    }

    /// Parse a type argument.
    fn parse_ty_arg(&mut self) -> ParseResult<AstNode<TyArg>> {
        let start = self.next_pos();

        let macros = self.parse_macro_invocations(MacroKind::Ast)?;

        // Here we have to essentially try and parse a identifier. If this is the
        // case and then there is a colon present then we
        // have a named field.
        let (name, ty) = match (self.peek(), self.peek_second()) {
            (
                Some(Token { kind: TokenKind::Ident(_), .. }),
                Some(Token { kind: TokenKind::Eq | TokenKind::Colon, .. }),
            ) => {
                // If the 3rd token is a colon, then this is a pure type
                // without a name...
                if matches!(self.peek_nth(2), Some(Token { kind: TokenKind::Colon, .. })) {
                    (None, self.parse_ty()?)
                } else {
                    let ident = self.parse_name()?;
                    self.skip_token(); // :

                    (Some(ident), self.parse_ty()?)
                }
            }
            _ => (None, self.parse_ty()?),
        };

        Ok(self.node_with_joined_span(TyArg { name, ty, macros }, start))
    }

    /// Parses a [Ty::Fn] which involves a parenthesis token tree with some
    /// arbitrary number of comma separated types followed by a return
    /// [Ty] that is preceded by an `thin-arrow` (->) after the
    /// parentheses. e.g. `(i32) -> str`
    fn parse_fn_or_tuple_ty(&mut self) -> ParseResult<Ty> {
        let mut gen = self.parse_delim_tree(Delimiter::Paren, None)?;
        let mut params = AstNodes::empty(gen.span());

        match gen.peek() {
            // Handle special case where there is only one comma and no following items...
            // Special edge case for '(,)' or an empty tuple type...
            Some(token) if token.has_kind(TokenKind::Comma) && gen.stream.len() == 1 => {
                gen.skip_token();
            }
            _ => {
                params = gen.parse_nodes(|g| g.parse_ty_arg(), |g| g.parse_token(TokenKind::Comma));
            }
        };

        // Here we check that the token tree has a comma at the end to later determine
        // if this is a `TupleType`...
        let gen_has_comma =
            !gen.stream.is_empty() && gen.token_at(gen.offset() - 1).has_kind(TokenKind::Comma);
        self.consume_gen(gen);

        // If there is an arrow '=>', then this must be a function type
        match self.peek_resultant_fn(|g| g.parse_thin_arrow()) {
            Some(_) => {
                // Parse the return type here, and then give the function name
                Ok(Ty::Fn(FnTy { params, return_ty: self.parse_ty()? }))
            }
            None => {
                // If there is only one entry in the params, and the last token in the entry is
                // not a comma then we can just return the inner type
                if gen_has_comma && params.len() == 1 && params[0].name.is_none() {
                    let field = params.nodes.pop().unwrap().into_body();
                    return Ok(field.ty.into_body());
                }

                Ok(Ty::Tuple(TupleTy { entries: params }))
            }
        }
    }

    /// Parses a [Ty::TyFn] with the pre-condition that the initial
    /// subject type is parsed and passed into the function. This function
    /// only deals with the argument part of the function.
    fn parse_ty_fn(&mut self) -> ParseResult<Ty> {
        // Since this is only called from `parse_singular_type` we know that this should
        // only be fired when the next token is a an `<`
        debug_assert!(matches!(self.current_token(), Token { kind: TokenKind::Lt, .. }));

        let mut arg_span = self.current_pos();
        let mut args = thin_vec![];

        loop {
            let span = self.current_pos();

            let macros = self.parse_macro_invocations(MacroKind::Ast)?;
            let name = self.parse_name()?;

            let ty = match self.parse_token_fast(TokenKind::Colon) {
                Some(_) => match self.peek() {
                    // Don't try and parse a type if an '=' is followed straight after
                    Some(tok) if tok.has_kind(TokenKind::Eq) => None,
                    _ => Some(self.parse_ty()?),
                },
                None => None,
            };

            let default = match self.parse_token_fast(TokenKind::Eq) {
                Some(_) => Some(self.parse_ty()?),
                None => None,
            };

            args.push(self.node_with_span(
                Param {
                    name: Some(name),
                    ty,
                    default: default.map(|node| {
                        let span = node.byte_range();
                        self.node_with_span(Expr::Ty(TyExpr { ty: node }), span)
                    }),
                    origin: ParamOrigin::TyFn,
                    macros,
                },
                span,
            ));

            // Now consider if the bound is closing or continuing with a comma...
            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    self.skip_token();
                }
                Some(token) if token.has_kind(TokenKind::Gt) => {
                    self.skip_token();
                    arg_span = arg_span.join(self.current_pos());

                    break;
                }
                Some(token) => self.err(
                    ParseErrorKind::UnExpected,
                    Some(TokenKindVector::from_vec(smallvec![TokenKind::Comma, TokenKind::Gt])),
                    Some(token.kind),
                )?,
                None => self.unexpected_eof()?,
            }
        }

        // Now pass the return type
        self.parse_thin_arrow()?;
        let return_ty = self.parse_ty()?;

        Ok(Ty::TyFn(TyFn { params: self.nodes_with_span(args, arg_span), return_ty }))
    }
}
