//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_token::{delimiter::Delimiter, keyword::Keyword, TokenKind};
use hash_utils::thin_vec::thin_vec;

use super::AstGen;
use crate::{
    diagnostics::error::{ParseErrorKind, ParseResult},
    parser::TyParamOrigin,
};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a [StructDef]. The keyword `struct` begins the construct and is
    /// followed by parentheses with inner struct fields defined.
    pub fn parse_struct_def(&mut self) -> ParseResult<StructDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Struct)));

        let def_kind = TyParamOrigin::Struct;
        let ty_params = self.parse_optional_ty_params(def_kind)?;

        let mut gen = self
            .parse_delim_tree(Delimiter::Paren, Some(ParseErrorKind::TypeDefinition(def_kind)))?;

        let fields = gen.parse_nodes(
            |g| g.parse_def_param(ParamOrigin::Struct),
            |g| g.parse_token(TokenKind::Comma),
        );
        self.consume_gen(gen);

        Ok(StructDef { ty_params, fields })
    }

    /// Parse an [EnumDef]. The keyword `enum` begins the construct and is
    /// followed by parentheses with inner enum fields defined.
    pub fn parse_enum_def(&mut self) -> ParseResult<EnumDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Enum)));

        let def_kind = TyParamOrigin::Enum;
        let ty_params = self.parse_optional_ty_params(def_kind)?;

        let mut gen = self
            .parse_delim_tree(Delimiter::Paren, Some(ParseErrorKind::TypeDefinition(def_kind)))?;

        let entries =
            gen.parse_nodes(|g| g.parse_enum_def_entry(), |g| g.parse_token(TokenKind::Comma));
        self.consume_gen(gen);

        Ok(EnumDef { ty_params, entries })
    }

    /// Parse an [EnumDefEntry].
    pub fn parse_enum_def_entry(&mut self) -> ParseResult<AstNode<EnumDefEntry>> {
        let start = self.current_pos();
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;

        let name = self.parse_name()?;
        let name_span = name.byte_range();
        let mut fields = self.nodes_with_span(thin_vec![], name_span);

        if matches!(self.peek(), Some(token) if token.is_paren_tree()) {
            let mut gen = self.parse_delim_tree(Delimiter::Paren, None)?;
            fields = gen.parse_nodes(
                |g| g.parse_def_param(ParamOrigin::EnumVariant),
                |g| g.parse_token(TokenKind::Comma),
            );
            fields.set_span(gen.span());
            self.consume_gen(gen);
        }

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

    /// Parses an nominal definition type field, which could either be a named
    /// or un-named field. The un-named field is just a specified type,
    /// whilst a named variant, is a specified name and then an optional
    /// type annotation and a default value.
    pub(crate) fn parse_def_param(&mut self, origin: ParamOrigin) -> ParseResult<AstNode<Param>> {
        let start = self.next_pos();
        let macros = self.parse_macro_invocations(MacroKind::Ast)?;

        // Try and parse the name and type
        let (name, ty) = match self.peek_second() {
            Some(token) if token.has_kind(TokenKind::Colon) => {
                let name = Some(self.parse_name()?);
                self.skip_token();

                // Now try and parse a type if the next token permits it...
                let ty = match self.peek() {
                    Some(token) if matches!(token.kind, TokenKind::Eq) => None,
                    _ => Some(self.parse_ty()?),
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

        Ok(self.node_with_joined_span(Param { name, ty, default, origin, macros }, start))
    }

    /// Parse a [TyFnDef]. Type functions specify logic at the type
    /// level on expressions such as struct, enum, function, and trait
    /// definitions.
    pub fn parse_ty_fn_def(&mut self) -> ParseResult<TyFnDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Lt));

        let params = self.parse_ty_params(TyParamOrigin::TyFn)?;

        // see if we need to add a return ty...
        let return_ty = match self.peek_resultant_fn(|g| g.parse_thin_arrow()) {
            Some(_) => Some(self.parse_ty()?),
            None => None,
        };

        // Now that we parse the bound, we're expecting a fat-arrow and then some
        // expression
        self.parse_arrow()?;
        let ty_fn_body = self.parse_expr_with_precedence(0)?;

        Ok(TyFnDef { params, return_ty, ty_fn_body })
    }

    /// Parse a [TraitDef]. A [TraitDef] is essentially a block prefixed with
    /// `trait` that contains definitions or attach expressions to a trait.
    pub fn parse_trait_def(&mut self) -> ParseResult<TraitDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Trait)));

        let ty_params = self.parse_optional_ty_params(TyParamOrigin::Trait)?;

        Ok(TraitDef { members: self.parse_exprs_from_braces()?, ty_params })
    }

    /// Parse a `mod` block, with optional type parameters.
    pub(crate) fn parse_mod_def(&mut self) -> ParseResult<ModDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Mod)));

        let ty_params = self.parse_optional_ty_params(TyParamOrigin::Mod)?;
        let block = self.parse_body_block()?;

        Ok(ModDef { block, ty_params })
    }

    /// Parse a `impl` block, with optional type parameters.
    pub(crate) fn parse_impl_def(&mut self) -> ParseResult<ImplDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Impl)));

        let ty_params = self.parse_optional_ty_params(TyParamOrigin::Impl)?;
        let block = self.parse_body_block()?;

        Ok(ImplDef { block, ty_params })
    }
}
