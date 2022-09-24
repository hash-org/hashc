//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_token::{delimiter::Delimiter, keyword::Keyword, TokenKind, TokenKindVector};
use smallvec::smallvec;

use super::AstGen;
use crate::diagnostics::{
    error::{ParseErrorKind, ParseResult},
    TyArgumentKind,
};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a [StructDef]. The keyword `struct` begins the construct and is
    /// followed by parentheses with inner struct fields defined.
    pub fn parse_struct_def(&mut self) -> ParseResult<StructDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Struct)));

        let ty_params = self.parse_optional_ty_params()?;

        let mut gen = self.parse_delim_tree(
            Delimiter::Paren,
            Some(ParseErrorKind::TypeDefinition(TyArgumentKind::Struct)),
        )?;

        let fields = gen.parse_separated_fn(
            |g| g.parse_nominal_def_param(ParamOrigin::Struct),
            |g| g.parse_token(TokenKind::Comma),
        );
        self.consume_gen(gen);

        Ok(StructDef { ty_params, fields })
    }

    /// Parse an [EnumDef]. The keyword `enum` begins the construct and is
    /// followed by parentheses with inner enum fields defined.
    pub fn parse_enum_def(&mut self) -> ParseResult<EnumDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Enum)));

        let ty_params = self.parse_optional_ty_params()?;

        let mut gen = self.parse_delim_tree(
            Delimiter::Paren,
            Some(ParseErrorKind::TypeDefinition(TyArgumentKind::Enum)),
        )?;

        let entries = gen
            .parse_separated_fn(|g| g.parse_enum_def_entry(), |g| g.parse_token(TokenKind::Comma));
        self.consume_gen(gen);

        Ok(EnumDef { ty_params, entries })
    }

    /// Parse an [EnumDefEntry].
    pub fn parse_enum_def_entry(&mut self) -> ParseResult<AstNode<EnumDefEntry>> {
        let name = self.parse_name()?;
        let name_span = name.span();

        let mut fields = AstNodes::empty();

        if matches!(self.peek(), Some(token) if token.is_paren_tree()) {
            let mut gen = self.parse_delim_tree(Delimiter::Paren, None)?;
            fields = gen.parse_separated_fn(
                |g| g.parse_nominal_def_param(ParamOrigin::EnumVariant),
                |g| g.parse_token(TokenKind::Comma),
            );
            self.consume_gen(gen);
        }

        Ok(self.node_with_joined_span(EnumDefEntry { name, fields }, name_span))
    }

    /// Parses an nominal definition type field, which could either be a named
    /// or un-named field. The un-named field is just a specified type,
    /// whilst a named variant, is a specified name and then an optional
    /// type annotation and a default value.
    pub(crate) fn parse_nominal_def_param(
        &mut self,
        origin: ParamOrigin,
    ) -> ParseResult<AstNode<Param>> {
        let start = self.next_location();

        // Try and parse the name and type
        let (name, ty) = match self.peek_second() {
            Some(token) if token.has_kind(TokenKind::Colon) => {
                let name = Some(self.parse_name()?);

                // Now try and parse a type if the next token permits it...
                let ty = match self.parse_token_fast(TokenKind::Colon) {
                    Some(_) => match self.peek() {
                        Some(token) if matches!(token.kind, TokenKind::Eq | TokenKind::Comma) => {
                            None
                        }
                        _ => Some(self.parse_ty()?),
                    },
                    None => None,
                };

                (name, ty)
            }
            _ => (None, Some(self.parse_ty()?)),
        };

        // If `name` and or `type` is followed by an `=`. we disallow default values
        // for un-named fields.
        let default = match self.peek() {
            Some(token) if name.is_some() && token.has_kind(TokenKind::Eq) => {
                self.skip_token();
                Some(self.parse_expr_with_precedence(0)?)
            }
            _ => None,
        };

        Ok(self.node_with_joined_span(Param { name, ty, default, origin }, start))
    }

    /// Parse a [TyFnDef]. Type functions specify logic at the type
    /// level on expressions such as struct, enum, function, and trait
    /// definitions.
    pub fn parse_ty_fn_def(&mut self) -> ParseResult<TyFnDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Lt));

        let params = self.parse_ty_params()?;

        // see if we need to add a return ty...
        let return_ty = match self.peek_resultant_fn(|g| g.parse_thin_arrow()) {
            Some(_) => Some(self.parse_ty()?),
            None => None,
        };

        // Now that we parse the bound, we're expecting a fat-arrow and then some
        // expression
        self.parse_arrow()?;
        let body = self.parse_expr_with_precedence(0)?;

        Ok(TyFnDef { params, return_ty, body })
    }

    // Parse a [Param] which consists the name of the argument and
    // then any specified bounds on the argument which are essentially types
    // that are separated by a `~`
    fn parse_ty_fn_def_param(&mut self) -> ParseResult<AstNode<Param>> {
        let start = self.current_location();
        let name = self.parse_name()?;

        // Now it's followed by a colon
        let ty = match self.parse_token_fast(TokenKind::Colon) {
            Some(_) => match self.peek() {
                Some(tok) if tok.has_kind(TokenKind::Eq) => None,
                _ => Some(self.parse_ty()?),
            },
            None => None,
        };

        // Parse a default type
        let default = match self.parse_token_fast(TokenKind::Eq) {
            Some(_) => Some(self.parse_ty()?),
            None => None,
        };

        Ok(self.node_with_joined_span(
            Param {
                name: Some(name),
                ty,
                default: default.map(|node| {
                    let span = node.span();
                    self.node_with_span(Expr::new(ExprKind::Ty(TyExpr(node))), span)
                }),
                origin: ParamOrigin::TyFn,
            },
            start,
        ))
    }

    /// Parse a [TraitDef]. A [TraitDef] is essentially a block prefixed with
    /// `trait` that contains definitions or attach expressions to a trait.
    pub fn parse_trait_def(&mut self) -> ParseResult<TraitDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Trait)));

        let ty_params = self.parse_optional_ty_params()?;

        Ok(TraitDef { members: self.parse_exprs_from_braces()?, ty_params })
    }

    /// Parse optional type [Param]s, if the next token is not a
    /// `<`, the function will return an empty [AstNodes<Param>].
    #[inline]
    pub(crate) fn parse_optional_ty_params(&mut self) -> ParseResult<AstNodes<Param>> {
        match self.peek() {
            Some(tok) if tok.has_kind(TokenKind::Lt) => {
                self.skip_token();
                self.parse_ty_params()
            }
            _ => Ok(AstNodes::new(vec![], None)),
        }
    }

    /// Parse a collection of type [Param]s which can appear on nominal
    /// definitions, and trait definitions.
    fn parse_ty_params(&mut self) -> ParseResult<AstNodes<Param>> {
        let mut params = AstNodes::empty();

        // Flag denoting that we were able to parse the ending `>` within the function
        // def arg
        let mut param_ending = false;

        while let Some(param) = self.peek_resultant_fn_mut(|g| g.parse_ty_fn_def_param()) {
            params.nodes.push(param);

            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    self.skip_token();
                }
                Some(token) if token.has_kind(TokenKind::Gt) => {
                    self.skip_token();
                    param_ending = true;
                    break;
                }
                token => self.err_with_location(
                    ParseErrorKind::Expected,
                    Some(TokenKindVector::from_vec(smallvec![TokenKind::Comma, TokenKind::Gt])),
                    token.map(|t| t.kind),
                    token.map_or_else(|| self.next_location(), |t| t.span),
                )?,
            }
        }

        // So if we failed to parse even a `>` we should report this...
        if !param_ending {
            // Here we encountered a trailing comma, so now we have to account for
            // the `>` being after
            if matches!(self.peek(), Some(tok) if tok.has_kind(TokenKind::Gt)) {
                self.skip_token();
            } else {
                self.err_with_location(
                    ParseErrorKind::Expected,
                    Some(TokenKindVector::singleton(TokenKind::Gt)),
                    self.peek().map(|tok| tok.kind),
                    self.next_location(),
                )?;
            }
        }

        Ok(params)
    }
}
