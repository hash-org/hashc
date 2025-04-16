//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_reporting::diagnostic::{DiagnosticsMut, HasDiagnosticsMut};
use hash_source::identifier::IDENTS;
use hash_token::{Token, TokenKind, delimiter::Delimiter, keyword::Keyword};
use hash_utils::thin_vec::thin_vec;

use super::AstGen;
use crate::diagnostics::{
    error::{ParseErrorKind, ParseResult},
    expected::ExpectedItem,
    warning::{ParseWarning, WarningKind},
};

impl AstGen<'_> {
    /// Parse a [Ty]. This includes all forms of a [Ty]. This function
    /// does not deal with any kind of [Ty] annotation or [ImplicitFnDef]
    /// syntax.
    pub(crate) fn parse_ty(&mut self) -> ParseResult<AstNode<Ty>> {
        self.parse_ty_with_precedence(0)
    }

    /// Parse a [Ty] with precedence in mind. The type notation contains
    /// [BinTyOp] operators which are binary operators for type terms. This
    /// function implements the same precedence algorithm for correctly
    /// forming binary type expressions.
    fn parse_ty_with_precedence(&mut self, min_prec: u8) -> ParseResult<AstNode<Ty>> {
        let (mut lhs, lhs_span) = self.track_span(|this| this.parse_singular_ty())?;

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
                    self.skip(consumed_tokens);

                    // Now recurse and get the `rhs` of the operator.
                    let rhs = self.parse_ty_with_precedence(r_prec)?;

                    // transform the operator into an `UnaryTy` or `EqualityTy` based on the
                    // operator
                    lhs = match op {
                        BinTyOp::Union => {
                            self.node_with_joined_span(Ty::Union(UnionTy { lhs, rhs }), lhs_span)
                        }
                        BinTyOp::Equality => self
                            .node_with_joined_span(Ty::Equality(EqualityTy { lhs, rhs }), lhs_span),
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
            self.make_err(
                ParseErrorKind::ExpectedTy,
                ExpectedItem::Type,
                None,
                Some(self.eof_pos()),
            )
        })?;

        let mut multi_ty_components = true;
        let span = token.span;

        // Parse the initial part of the type
        let mut ty = match token.kind {
            TokenKind::Amp => {
                self.skip_fast(TokenKind::Amp);

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
            ident @ TokenKind::Ident(id) => {
                self.skip_fast(ident);

                let name = self.node_with_span(Name { ident: id }, span);
                Ty::Named(NamedTy { name })
            }

            // Expression in the type.
            TokenKind::Tree(Delimiter::Brace, _) => self.in_tree(Delimiter::Brace, None, |g| {
                let expr = g.parse_expr_with_precedence(0)?;
                Ok(Ty::Expr(ExprTy { expr }))
            })?,

            // Array type
            TokenKind::Tree(Delimiter::Bracket, _) => {
                let (inner, len) = self.in_tree(Delimiter::Bracket, None, |g| {
                    // @@ErrorRecovery: Investigate introducing `Err` variant into types...
                    let inner_type = g.parse_ty()?;

                    // Optionally, the user may specify a size for the array type by
                    // using a `;` followed by an expression that evaluates to a]
                    // constant integer.
                    let len = if g.peek_kind() == Some(TokenKind::Semi) {
                        g.skip_fast(TokenKind::Semi);
                        Some(g.parse_expr()?)
                    } else {
                        None
                    };

                    Ok((inner_type, len))
                })?;

                Ty::Array(ArrayTy { inner, len })
            }

            // Tuple or function type
            TokenKind::Tree(Delimiter::Paren, _) => {
                multi_ty_components = false;
                self.parse_fn_or_tuple_ty()?
            }

            // Special syntax for the never type `!`
            TokenKind::Exclamation => {
                self.skip_fast(TokenKind::Exclamation);

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

            // Parse a token macro invocation
            TokenKind::At => {
                let token_macro = self.parse_token_macro_invocation()?;
                Ty::TokenMacro(token_macro)
            }

            // Type function, which is a collection of arguments enclosed in `<...>` and then
            // followed by a return type
            TokenKind::Lt => {
                multi_ty_components = false;
                self.parse_implicit_fn()?
            }

            // This allows for the user to use the shorthand for literal types within
            // type positions, if the token is a primitive literal, then we parse it as
            // a expression in a type.
            kind if kind.is_lit() => {
                let expr = self.parse_expr()?;
                Ty::Expr(ExprTy { expr })
            }

            kind => self.err_with_location(
                ParseErrorKind::ExpectedTy,
                ExpectedItem::Type,
                Some(kind),
                span,
            )?,
        };

        // Deal with type function call, or type access
        while multi_ty_components && let Some(token) = self.peek() {
            ty = match token.kind {
                TokenKind::Lt => {
                    self.skip_fast(TokenKind::Lt);

                    let ty = self.node_with_joined_span(ty, span);
                    Ty::ImplicitCall(ImplicitFnCall {
                        subject: self.node_with_joined_span(Expr::Ty(TyExpr { ty }), span),
                        args: self.parse_ty_args(true)?,
                    })
                }
                // Function syntax which allow to express `U -> T` whilst implying `(U -> T)`
                TokenKind::ThinArrow => {
                    self.skip_fast(TokenKind::ThinArrow);
                    let return_ty = self.parse_ty()?;

                    let ty = self.node_with_joined_span(ty, span);
                    let param = self.node_with_span(
                        Param {
                            name: None,
                            default: None,
                            ty: Some(ty),
                            // ##Note: this will always be none since the above function
                            // will parse the args and then apply it to us as the subject.
                            //
                            // So if `#foo U -> T` is present, we parse as `TyMacroInvocation {
                            // subject: U -> T, macros: #foo }`
                            macros: None,
                        },
                        span,
                    );

                    let params = self.nodes_with_span(thin_vec![param], span);
                    Ty::Fn(FnTy { params: self.make_params(params, ParamOrigin::Fn), return_ty })
                }

                TokenKind::Access => {
                    self.skip_fast(TokenKind::Access);

                    Ty::Access(AccessTy {
                        subject: self.node_with_joined_span(ty, span),
                        property: self.parse_name()?,
                    })
                }
                _ => break,
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

        // Shortcut, if we get no arguments, then we can avoid looping:
        // if matches!(self.peek(), Some(Token { kind: TokenKind::Gt, .. })) {
        //     self.skip_fast(TokenKind::Gt);
        //     return Ok(self.nodes_with_span(ty_args, start));
        // }

        loop {
            ty_args.push(self.parse_ty_arg()?);

            // Now consider if the bound is closing or continuing with a comma...
            match self.peek_kind() {
                Some(TokenKind::Comma) => {
                    self.skip_fast(TokenKind::Comma);

                    // Handle for the trailing comma case.
                    if matches!(self.peek_kind(), Some(TokenKind::Gt)) {
                        self.skip_fast(TokenKind::Gt);
                        break;
                    }
                }
                Some(TokenKind::Gt) => {
                    self.skip_fast(TokenKind::Gt);
                    break;
                }
                Some(kind) => self.err(
                    ParseErrorKind::UnExpected,
                    ExpectedItem::Comma | ExpectedItem::Gt,
                    Some(kind),
                )?,
                None => self.unexpected_eof()?,
            }
        }

        // Update the location of the type bound to reflect the '<' and '>' tokens...
        Ok(self.nodes_with_joined_span(ty_args, start))
    }

    /// Parse a type argument.
    fn parse_ty_arg(&mut self) -> ParseResult<AstNode<TyArg>> {
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;
        let start = self.current_pos();

        // Here we have to essentially try and parse a identifier. If this is the
        // case and then there is a colon present then we
        // have a named field.
        let (name, ty) = match (self.peek(), self.peek_second()) {
            (
                Some(Token { kind: TokenKind::Ident(_), .. }),
                Some(Token { kind: TokenKind::Eq, .. }),
            ) => {
                let ident = self.parse_name()?;
                self.skip_fast(TokenKind::Eq);

                (Some(ident), self.parse_ty()?)
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
        let (mut params, has_comma) = self.in_tree(Delimiter::Paren, None, |g| {
            let params = match g.peek_kind() {
                // Handle special case where there is only one comma and no following items...
                // Special edge case for '(,)' or an empty tuple type...
                Some(TokenKind::Comma) if g.len() == 1 => {
                    g.skip_fast(TokenKind::Comma);
                    g.nodes_with_span(thin_vec![], g.range())
                }
                _ => g.parse_nodes(
                    |g| g.parse_ty_tuple_or_fn_param(),
                    |g| g.parse_token(TokenKind::Comma),
                ),
            };

            // Abort early if we encountered some kind of error along the way,
            // although I would think when the `gen` is consumed then we can
            // send up all of the errors to the parent generator?
            if g.diagnostics.has_errors() {
                let err = g.diagnostics.errors.pop().unwrap();
                return Err(err);
            }

            // Here we check that the token tree has a comma at the end to later determine
            // if this is a `TupleTy`...
            let gen_has_comma = !g.is_empty() && g.previous_token().has_kind(TokenKind::Comma);
            Ok((params, gen_has_comma))
        })?;

        // If there is an arrow '=>', then this must be a function type
        match self.peek_resultant_fn(|g| g.parse_token(TokenKind::ThinArrow)) {
            Some(_) => {
                let params = self.make_params(params, ParamOrigin::Fn);
                // Parse the return type here, and then give the function name
                Ok(Ty::Fn(FnTy { params, return_ty: self.parse_ty()? }))
            }
            None => {
                // If there is only one entry in the params, and the last token in the entry is
                // not a comma then we can just return the inner type
                if has_comma && params.len() == 1 && params[0].name.is_none() {
                    let field = params.nodes.pop().unwrap().into_body();
                    return Ok(field.ty.unwrap().into_body());
                }

                let params = self.make_params(params, ParamOrigin::Tuple);
                Ok(Ty::Tuple(TupleTy { entries: params }))
            }
        }
    }

    /// Parses a [Ty::ImplicitFn] with the pre-condition that the initial
    /// subject type is parsed and passed into the function. This function
    /// only deals with the argument part of the function.
    fn parse_implicit_fn(&mut self) -> ParseResult<Ty> {
        debug_assert!(matches!(self.current_token(), Token { kind: TokenKind::Lt, .. }));
        // Since this is only called from `parse_singular_type` we know that this should
        // only be fired when the next token is a an `<`
        let params = self.parse_ty_params(TyParamOrigin::ImplicitFn)?;

        // Now pass the return type
        self.parse_token(TokenKind::ThinArrow)?;
        let return_ty = self.parse_ty()?;

        Ok(Ty::ImplicitFn(ImplicitFnTy { params, return_ty }))
    }

    /// Parse optional type [Param]s, if the next token is not a
    /// `<`, the function will return an empty [AstNodes<Param>].
    #[inline(always)]
    pub(crate) fn parse_optional_ty_params(
        &mut self,
        def_kind: TyParamOrigin,
    ) -> ParseResult<Option<AstNode<TyParams>>> {
        match self.peek_kind() {
            Some(TokenKind::Lt) => Ok(Some(self.parse_ty_params(def_kind)?)),
            _ => Ok(None),
        }
    }

    /// Construct the [TyParams] from the parsed [`AstNodes<TyParam>`]. This is
    /// just a utility function to wrap the nodes in the [TyParams] struct.
    fn make_ty_params(
        &self,
        params: AstNodes<TyParam>,
        origin: TyParamOrigin,
    ) -> AstNode<TyParams> {
        let id = params.id();
        AstNode::with_id(TyParams { params, origin }, id)
    }

    /// Parse a [TyParams] which consists of a list of [TyParam]s.
    pub(crate) fn parse_ty_params(
        &mut self,
        origin: TyParamOrigin,
    ) -> ParseResult<AstNode<TyParams>> {
        let start_span = self.current_pos();
        self.skip_fast(TokenKind::Lt);

        let mut params = thin_vec![];

        // Shortcut, if we get no arguments, then we can avoid looping:
        if matches!(self.peek_kind(), Some(TokenKind::Gt)) {
            self.skip_fast(TokenKind::Gt);

            // Emit a warning here if there were no params
            let span = start_span.join(self.previous_pos());
            self.add_warning(ParseWarning::new(
                WarningKind::UselessTyParams { origin },
                self.make_span(span),
            ));

            let params = self.nodes_with_span(params, span);
            return Ok(self.make_ty_params(params, origin));
        }

        loop {
            params.push(self.parse_ty_param()?);

            match self.peek() {
                Some(Token { kind: TokenKind::Comma, .. }) => {
                    self.skip_fast(TokenKind::Comma);

                    // Handle for the trailing comma case.
                    if matches!(self.peek_kind(), Some(TokenKind::Gt)) {
                        self.skip_fast(TokenKind::Gt);
                        break;
                    }
                }
                Some(Token { kind: TokenKind::Gt, .. }) => {
                    self.skip_fast(TokenKind::Gt);
                    break;
                }
                token => self.err_with_location(
                    ParseErrorKind::UnExpected,
                    ExpectedItem::Comma | ExpectedItem::Gt,
                    token.map(|t| t.kind),
                    token.map_or_else(|| self.eof_pos(), |t| t.span),
                )?,
            }
        }

        let params = self.nodes_with_joined_span(params, start_span);
        Ok(self.make_ty_params(params, origin))
    }

    /// Parse a [TyParam] which can consist of an optional name, and a type.
    /// This is only intended for parameters that appear in function and tuple
    /// types. The other more broad function [`Self::parse_ty_param()`]  is for
    /// parsing type parameters with default values too,
    fn parse_ty_tuple_or_fn_param(&mut self) -> ParseResult<AstNode<Param>> {
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;
        let start = self.current_pos();

        let (name, ty) = match (self.peek(), self.peek_second()) {
            (
                Some(Token { kind: TokenKind::Ident(_), .. }),
                Some(Token { kind: TokenKind::Colon, .. }),
            ) => {
                let ident = self.parse_name()?;
                self.skip_fast(TokenKind::Colon);
                (Some(ident), Some(self.parse_ty()?))
            }
            _ => (None, Some(self.parse_ty()?)),
        };

        Ok(self.node_with_joined_span(Param { name, ty, default: None, macros }, start))
    }

    /// Parse a [TyParam] which consists the name of the parameter, optional
    /// type annotation and an optional "default" value for the parameter.
    fn parse_ty_param(&mut self) -> ParseResult<AstNode<TyParam>> {
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;
        let token = *self.current_token();

        // We always get a name for this kind of parameter.
        let name = Some(self.parse_name().map_err(|_| {
            self.make_err(
                ParseErrorKind::UnExpected,
                ExpectedItem::Ident | ExpectedItem::Gt,
                Some(token.kind),
                Some(token.span),
            )
        })?);

        // Try and parse the name and type
        let ty = match self.peek_kind() {
            Some(TokenKind::Colon) => {
                self.skip_fast(TokenKind::Colon);

                // Now try and parse a type if the next token permits it...
                match self.peek() {
                    Some(token) if matches!(token.kind, TokenKind::Eq) => None,
                    _ => Some(self.parse_ty()?),
                }
            }
            _ => None,
        };

        // Parse a default type
        let default = match self.parse_token_fast(TokenKind::Eq) {
            Some(_) => Some(self.parse_ty()?),
            None => None,
        };

        Ok(self.node_with_joined_span(TyParam { name, ty, default, macros }, token.span))
    }
}
