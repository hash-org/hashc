//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_token::{delimiter::Delimiter, keyword::Keyword, TokenKind};

use super::AstGen;
use crate::{
    diagnostics::error::{ParseErrorKind, ParseResult},
    parser::TyParamOrigin,
};

impl<'s> AstGen<'s> {
    /// Construct the [Params] from the parsed [`AstNodes<Param>`]. This is
    /// just a utility function to wrap the nodes in the [Params] struct.
    pub fn make_params(&self, params: AstNodes<Param>, origin: ParamOrigin) -> AstNode<Params> {
        let id = params.id();
        AstNode::with_id(Params { params, origin }, id)
    }

    /// Parse a [StructDef]. The keyword `struct` begins the construct and is
    /// followed by parentheses with inner struct fields defined.
    pub fn parse_struct_def(&mut self) -> ParseResult<StructDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Struct)));
        self.skip_fast(); // `struct`

        let def_kind = TyParamOrigin::Struct;
        let ty_params = self.parse_optional_ty_params(def_kind)?;
        let fields = self.parse_params(ParamOrigin::Struct)?;

        Ok(StructDef { ty_params, fields })
    }

    /// Parse an [EnumDef]. The keyword `enum` begins the construct and is
    /// followed by parentheses with inner enum fields defined.
    pub fn parse_enum_def(&mut self) -> ParseResult<EnumDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Enum)));
        self.skip_fast(); // `enum`

        let def_kind = TyParamOrigin::Enum;
        let ty_params = self.parse_optional_ty_params(def_kind)?;

        let entries =
            self.in_tree(Delimiter::Paren, Some(ParseErrorKind::TyDef(def_kind)), |gen| {
                Ok(gen
                    .parse_nodes(|g| g.parse_enum_def_entry(), |g| g.parse_token(TokenKind::Comma)))
            })?;

        Ok(EnumDef { ty_params, entries })
    }

    /// Parse an [EnumDefEntry].
    pub fn parse_enum_def_entry(&mut self) -> ParseResult<AstNode<EnumDefEntry>> {
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;
        let start = self.current_pos();
        let name = self.parse_name()?;

        let fields = if matches!(self.peek(), Some(token) if token.is_paren_tree()) {
            Some(self.parse_params(ParamOrigin::EnumVariant)?)
        } else {
            None
        };

        // Attempt to parse an optional type for the variant
        // Now try and parse a type if the next token permits it...
        let ty = match self.parse_token_fast(TokenKind::Colon) {
            Some(_) => match self.peek() {
                Some(token) if matches!(token.kind, TokenKind::Comma) => None,
                _ => Some(self.parse_ty()?),
            },
            None => None,
        };

        Ok(self.node_with_joined_span(EnumDefEntry { name, fields, ty, macros }, start))
    }

    pub(crate) fn parse_params(&mut self, origin: ParamOrigin) -> ParseResult<AstNode<Params>> {
        // We add a little bit more context if the param-origin is a type definition
        // item.
        let err_ctx = match origin {
            ParamOrigin::Struct => Some(ParseErrorKind::TyDef(TyParamOrigin::Struct)),
            ParamOrigin::EnumVariant => Some(ParseErrorKind::TyDef(TyParamOrigin::Enum)),
            _ => None,
        };

        let params = self.in_tree(Delimiter::Paren, err_ctx, |gen| {
            Ok(gen.parse_nodes(|g| g.parse_param(origin), |g| g.parse_token(TokenKind::Comma)))
        })?;
        Ok(self.make_params(params, origin))
    }

    /// Parses an nominal definition type field, which could either be a named
    /// or un-named field. The un-named field is just a specified type,
    /// whilst a named variant, is a specified name and then an optional
    /// type annotation and a default value.
    pub(crate) fn parse_param(&mut self, origin: ParamOrigin) -> ParseResult<AstNode<Param>> {
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;
        let start = self.current_pos();

        // If this is a function parameter, we always parse a name!
        let (name, ty) = if matches!(origin, ParamOrigin::Fn) {
            let name = Some(self.parse_name()?);

            // Parse an optional type annotation...
            let ty = match self.peek_kind() {
                Some(TokenKind::Colon) => {
                    self.skip_fast(); // `:`
                    Some(self.parse_ty()?)
                }
                _ => None,
            };

            (name, ty)
        } else {
            match self.peek_second() {
                Some(token) if token.has_kind(TokenKind::Colon) => {
                    let name = Some(self.parse_name()?);
                    self.skip_fast(); // `:`

                    // Now try and parse a type if the next token permits it...
                    let ty = match self.peek_kind() {
                        Some(TokenKind::Eq) => None,
                        _ => Some(self.parse_ty()?),
                    };

                    (name, ty)
                }
                _ => (None, Some(self.parse_ty()?)),
            }
        };

        // If `name` and or `type` is followed by an `=`. we disallow default values
        // for un-named fields.
        let default = match self.peek_kind() {
            Some(TokenKind::Eq) if name.is_some() => {
                self.skip_fast(); // `=`
                Some(self.parse_expr_with_precedence(0)?)
            }
            _ => None,
        };

        Ok(self.node_with_joined_span(Param { name, ty, default, macros }, start))
    }

    /// Parse a [TyFnDef]. Type functions specify logic at the type
    /// level on expressions such as struct, enum, function, and trait
    /// definitions.
    pub fn parse_ty_fn_def(&mut self) -> ParseResult<TyFnDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Lt));
        let params = self.parse_ty_params(TyParamOrigin::TyFn)?;

        // see if we need to add a return ty...
        let return_ty = match self.peek_resultant_fn(|g| g.parse_token(TokenKind::ThinArrow)) {
            Some(_) => Some(self.parse_ty()?),
            None => None,
        };

        // Now that we parse the bound, we're expecting a fat-arrow and then some
        // expression
        self.parse_token(TokenKind::FatArrow)?;
        let ty_fn_body = self.parse_expr_with_precedence(0)?;

        Ok(TyFnDef { params, return_ty, ty_fn_body })
    }

    /// Parse a [TraitDef]. A [TraitDef] is essentially a block prefixed with
    /// `trait` that contains definitions or attach expressions to a trait.
    pub fn parse_trait_def(&mut self) -> ParseResult<TraitDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Trait)));
        self.skip_fast(); // `trait`

        let ty_params = self.parse_optional_ty_params(TyParamOrigin::Trait)?;

        Ok(TraitDef { members: self.parse_exprs_from_braces()?, ty_params })
    }

    /// Parse a `mod` block, with optional type parameters.
    pub(crate) fn parse_mod_def(&mut self) -> ParseResult<ModDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Mod)));
        self.skip_fast(); // `mod`

        let ty_params = self.parse_optional_ty_params(TyParamOrigin::Mod)?;
        let block = self.parse_body_block()?;

        Ok(ModDef { block, ty_params })
    }

    /// Parse a `impl` block, with optional type parameters.
    pub(crate) fn parse_impl_def(&mut self) -> ParseResult<ImplDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Impl)));
        self.skip_fast(); // `impl`

        let ty_params = self.parse_optional_ty_params(TyParamOrigin::Impl)?;
        let block = self.parse_body_block()?;

        Ok(ImplDef { block, ty_params })
    }
}
