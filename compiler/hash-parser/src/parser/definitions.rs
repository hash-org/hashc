//! Hash Compiler AST generation sources. This file contains the sources to the
//! logic that transforms tokens into an AST.
use hash_ast::ast::*;
use hash_token::{delimiter::Delimiter, keyword::Keyword, TokenKind, TokenKindVector};

use crate::parser::error::TyArgumentKind;

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    /// Parse a [StructDef]. The keyword `struct` begins the construct and is
    /// followed by parentheses with inner struct fields defined.
    pub fn parse_struct_def(&self) -> AstGenResult<StructDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Struct)));

        let gen = self.parse_delim_tree(
            Delimiter::Paren,
            Some(AstGenErrorKind::TypeDefinition(TyArgumentKind::Struct)),
        )?;

        let entries = gen.parse_separated_fn(
            || gen.parse_struct_def_entry(),
            || gen.parse_token(TokenKind::Comma),
        )?;

        Ok(StructDef { entries })
    }

    /// Parse a [StructDefEntry].
    pub fn parse_struct_def_entry(&self) -> AstGenResult<AstNode<StructDefEntry>> {
        let name = self.parse_name()?;
        let name_span = name.span();

        let ty = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Colon) => {
                self.skip_token();
                Some(self.parse_type()?)
            }
            _ => None,
        };

        let default = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Eq) => {
                self.skip_token();

                Some(self.parse_expression_with_precedence(0)?)
            }
            _ => None,
        };

        Ok(self.node_with_joined_span(StructDefEntry { name, ty, default }, &name_span))
    }

    /// Parse an [EnumDef]. The keyword `enum` begins the construct and is
    /// followed by parentheses with inner enum fields defined.
    pub fn parse_enum_def(&self) -> AstGenResult<EnumDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Enum)));

        let gen = self.parse_delim_tree(
            Delimiter::Paren,
            Some(AstGenErrorKind::TypeDefinition(TyArgumentKind::Enum)),
        )?;

        let entries = gen.parse_separated_fn(
            || gen.parse_enum_def_entry(),
            || gen.parse_token(TokenKind::Comma),
        )?;

        Ok(EnumDef { entries })
    }

    /// Parse an [EnumDefEntry].
    pub fn parse_enum_def_entry(&self) -> AstGenResult<AstNode<EnumDefEntry>> {
        let name = self.parse_name()?;
        let name_span = name.span();

        let mut args = AstNodes::empty();

        if matches!(self.peek(), Some(token) if token.is_paren_tree()) {
            let gen = self.parse_delim_tree(Delimiter::Paren, None)?;
            args =
                gen.parse_separated_fn(|| gen.parse_type(), || gen.parse_token(TokenKind::Comma))?;
        }

        Ok(self.node_with_joined_span(EnumDefEntry { name, args }, &name_span))
    }

    /// Parse a [TyFnDef]. Type functions specify logic at the type
    /// level on expressions such as struct, enum, function, and trait
    /// definitions.
    pub fn parse_type_function_def(&self) -> AstGenResult<TyFnDef> {
        let mut params = AstNodes::empty();

        // We can't do this because the parse_separated_fn() function expects a token
        // tree and not the while tree:
        //
        // let args = self.parse_separated_fn(
        //     || self.parse_type_function_def_arg(),
        //     || self.parse_token_atom(TokenKind::Comma),
        // )?;
        //
        // And so instead we do this:
        //
        while let Some(param) = self.peek_resultant_fn(|| self.parse_type_function_def_arg()) {
            params.nodes.push(param);

            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    self.skip_token();
                }
                Some(token) if token.has_kind(TokenKind::Gt) => {
                    self.skip_token();
                    break;
                }
                token => self.error_with_location(
                    AstGenErrorKind::Expected,
                    Some(TokenKindVector::from_row(vec![TokenKind::Comma, TokenKind::Gt])),
                    token.map(|t| t.kind),
                    token.map_or_else(|| self.next_location(), |t| t.span),
                )?,
            }
        }

        // see if we need to add a return ty...
        let return_ty = match self.peek_resultant_fn(|| self.parse_thin_arrow()) {
            Some(_) => Some(self.parse_type()?),
            None => None,
        };

        // Now that we parse the bound, we're expecting a fat-arrow and then some
        // expression
        self.parse_arrow()?;
        let expr = self.parse_expression_with_precedence(0)?;

        Ok(TyFnDef { params, return_ty, expr })
    }

    // Parse a [TyFnDefParam] which consists the name of the argument and
    // then any specified bounds on the argument which are essentially types
    // that are separated by a `~`
    fn parse_type_function_def_arg(&self) -> AstGenResult<AstNode<TyFnDefParam>> {
        let start = self.current_location();
        let name = self.parse_name()?;

        // Now it's followed by a colon
        let ty = match self.parse_token_fast(TokenKind::Colon) {
            Some(_) => match self.peek() {
                Some(tok) if tok.has_kind(TokenKind::Eq) => None,
                _ => Some(self.parse_type()?),
            },
            None => None,
        };

        // Parse a default type
        let default = match self.parse_token_fast(TokenKind::Eq) {
            Some(_) => Some(self.parse_type()?),
            None => None,
        };

        Ok(self.node_with_joined_span(TyFnDefParam { name, ty, default }, &start))
    }

    /// Parse a [TraitDef]. A [TraitDef] is essentially a block prefixed with
    /// `trait` that contains definitions or attach expressions to a trait.
    pub fn parse_trait_def(&self) -> AstGenResult<TraitDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Trait)));

        Ok(TraitDef { members: self.parse_expressions_from_braces()? })
    }
}
