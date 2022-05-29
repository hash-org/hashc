//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_alloc::row;
use hash_ast::ast::*;
use hash_token::{delimiter::Delimiter, keyword::Keyword, Token, TokenKind, TokenKindVector};

use crate::parser::error::TyArgumentKind;

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// Parse a [StructDef]. The keyword `struct` begins the construct and is followed
    /// by parenthesees with inner struct fields defined.
    pub fn parse_struct_def(&self) -> AstGenResult<'c, StructDef<'c>> {
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
                    || gen.parse_struct_def_entry(),
                    || gen.parse_token(TokenKind::Comma),
                )?
            }
            token => self.error_with_location(
                AstGenErrorKind::TypeDefinition(TyArgumentKind::Struct),
                None,
                token.map(|t| t.kind),
                token.map_or_else(|| self.next_location(), |t| t.span),
            )?,
        };

        Ok(StructDef { entries })
    }

    /// Parse a [StructDefEntry].
    pub fn parse_struct_def_entry(&self) -> AstGenResult<'c, AstNode<'c, StructDefEntry<'c>>> {
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

    /// Parse an [EnumDef]. The keyword `enum` begins the construct and is followed
    /// by parenthesees with inner enum fields defined.
    pub fn parse_enum_def(&self) -> AstGenResult<'c, EnumDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Enum)));

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
                    || gen.parse_token(TokenKind::Comma),
                )?
            }
            token => self.error_with_location(
                AstGenErrorKind::TypeDefinition(TyArgumentKind::Enum),
                None,
                token.map(|t| t.kind),
                token.map_or_else(|| self.next_location(), |t| t.span),
            )?,
        };

        Ok(EnumDef { entries })
    }

    /// Parse an [EnumDefEntry].
    pub fn parse_enum_def_entry(&self) -> AstGenResult<'c, AstNode<'c, EnumDefEntry<'c>>> {
        let name = self.parse_name()?;
        let name_span = name.location();

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
                    gen.parse_token(TokenKind::Comma)?;
                }
            }
        }

        Ok(self.node_with_joined_span(EnumDefEntry { name, args }, &name_span))
    }

    /// Parse a [TypeFunctionDef]. Type functions specify logic at the type level on expressions such as
    /// struct, enum, function, and trait definitions.
    pub fn parse_type_function_def(&self) -> AstGenResult<'c, TypeFunctionDef<'c>> {
        let mut args = AstNodes::empty();

        // We can't do this because the parse_separated_fn() function expects a token tree and
        // not the while tree:
        //
        // let args = self.parse_separated_fn(
        //     || self.parse_type_function_def_arg(),
        //     || self.parse_token_atom(TokenKind::Comma),
        // )?;
        //
        // And so instead we do this:
        //
        while let Some(arg) = self.peek_resultant_fn(|| self.parse_type_function_def_arg()) {
            args.nodes.push(arg, &self.wall);

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
                    Some(TokenKindVector::from_row(row![
                        &self.wall;
                        TokenKind::Comma,
                        TokenKind::Gt
                    ])),
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

        // Now that we parse the bound, we're expecting a fat-arrow and then some expression
        self.parse_arrow()?;
        let expr = self.parse_expression_with_precedence(0)?;

        Ok(TypeFunctionDef {
            args,
            return_ty,
            expr,
        })
    }

    // Parse a [TypeFunctionDefArg] which consists the name of the argument and then any specified bounds
    // on the argument which are essentially types that are separated by a `~`
    fn parse_type_function_def_arg(&self) -> AstGenResult<'c, AstNode<'c, TypeFunctionDefArg<'c>>> {
        let start = self.current_location();
        let name = self.parse_name()?;

        // Now it's followed by a colon
        let ty = self
            .parse_token_fast(TokenKind::Colon)
            .map(|_| self.parse_type())
            .transpose()?;

        Ok(self.node_with_joined_span(TypeFunctionDefArg { name, ty }, &start))
    }

    /// Parse a [TraitDef]. A [TraitDef] is essentially a block prefixed with `trait` that contains
    /// definitions or attach expressions to a trait.
    pub fn parse_trait_def(&self) -> AstGenResult<'c, TraitDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Trait)));

        Ok(TraitDef {
            members: self.parse_expressions_from_braces()?,
        })
    }
}
