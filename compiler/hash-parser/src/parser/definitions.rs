//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_ast::ast::*;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use crate::parser::error::TyArgumentKind;

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// Parse a [StructDefinition] which includes the name of the struct with a
    /// ForAll to specify any bounds or and generic arguments to the struct, with
    /// zero or more struct fields. An example for a struct would be:
    ///
    /// Name := <T,Q> where eq<T> => struct( ... );
    /// ^^^^       ^──────^^─┬──^            ^^^
    /// Name of struct     For all          fields
    pub fn parse_struct_defn(
        &self,
        name: AstNode<'c, Name>,
        bound: Option<AstNode<'c, Bound<'c>>>,
    ) -> AstGenResult<'c, StructDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Struct)));

        let entries = match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                span,
            }) => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, *span);

                gen.parse_separated_fn(
                    || gen.parse_struct_defn_entry(),
                    || gen.parse_token_atom(TokenKind::Comma),
                )?
            }
            token => self.error(
                AstGenErrorKind::TyArgument(TyArgumentKind::Struct),
                Some(TokenKindVector::singleton(
                    &self.wall,
                    TokenKind::Delimiter(Delimiter::Paren, false),
                )),
                token.map(|tok| tok.kind),
            )?,
        };

        Ok(StructDef {
            name,
            bound,
            entries,
        })
    }

    /// Parse a [StructDefEntry].
    pub fn parse_struct_defn_entry(&self) -> AstGenResult<'c, AstNode<'c, StructDefEntry<'c>>> {
        let start = self.current_location();
        let name = self.parse_name()?;

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

        Ok(self.node_with_joined_span(StructDefEntry { name, ty, default }, &start))
    }

    /// Parse an enum definition. AST representation for an enum, An enum is constructed by
    /// a the keyword 'enum' followed by an identifier name, a for-all declaration,
    /// followed by some enum fields. An enumeration can be made of zero or more enum fields.
    /// For example, a declaration of an enum would be:
    ///
    /// Name := <T, Q> where Eq<T> => enum(...);
    /// ^^^^       ^──────^^─┬──^          ^^^
    /// Name of enum      For all         fields
    ///
    pub fn parse_enum_defn(
        &self,
        name: AstNode<'c, Name>,
        bound: Option<AstNode<'c, Bound<'c>>>,
    ) -> AstGenResult<'c, EnumDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Enum)));

        // now parse the optional type bound and the enum definition entries,
        // if a type bound is specified, then the definition of the struct should
        // be followed by an arrow ('=>')...
        let entries = match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Paren, tree_index),
                span,
            }) => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, *span);

                gen.parse_separated_fn(
                    || gen.parse_enum_def_entry(),
                    || gen.parse_token_atom(TokenKind::Comma),
                )?
            }
            token => self.error(
                AstGenErrorKind::TyArgument(TyArgumentKind::Enum),
                Some(TokenKindVector::singleton(
                    &self.wall,
                    TokenKind::Delimiter(Delimiter::Paren, false),
                )),
                token.map(|tok| tok.kind),
            )?,
        };

        Ok(EnumDef {
            name,
            bound,
            entries,
        })
    }

    /// Parse an [EnumDefEntry].
    pub fn parse_enum_def_entry(&self) -> AstGenResult<'c, AstNode<'c, EnumDefEntry<'c>>> {
        let name = self.parse_name()?;
        let name_location = name.location();

        let mut args = AstNodes::empty();

        if let Some(Token {
            kind: TokenKind::Tree(Delimiter::Paren, tree_index),
            span,
        }) = self.peek()
        {
            self.skip_token();
            args.span = Some(*span);
            let tree = self.token_trees.get(*tree_index).unwrap();

            let gen = self.from_stream(tree, *span);
            while gen.has_token() {
                let ty = gen.parse_type()?;
                args.nodes.push(ty, &self.wall);

                if gen.has_token() {
                    gen.parse_token_atom(TokenKind::Comma)?;
                }
            }
        }

        Ok(self.node_with_joined_span(EnumDefEntry { name, args }, &name_location))
    }
}
