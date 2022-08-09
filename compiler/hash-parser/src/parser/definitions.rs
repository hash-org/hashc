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
    pub fn parse_struct_def(&self) -> ParseResult<StructDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Struct)));

        let mut gen = self.parse_delim_tree(
            Delimiter::Paren,
            Some(ParseErrorKind::TypeDefinition(TyArgumentKind::Struct)),
        )?;

        let entries = gen.parse_separated_fn(
            |g| g.parse_struct_def_entry(),
            |g| g.parse_token(TokenKind::Comma),
        )?;

        Ok(StructDef { entries })
    }

    /// Parse a struct definition entry which is represented as a [Param].
    pub fn parse_struct_def_entry(&mut self) -> ParseResult<AstNode<Param>> {
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

                Some(self.parse_expr_with_precedence(0)?)
            }
            _ => None,
        };

        Ok(self.node_with_joined_span(
            Param { name, ty, default, origin: ParamOrigin::Struct },
            name_span,
        ))
    }

    /// Parse an [EnumDef]. The keyword `enum` begins the construct and is
    /// followed by parentheses with inner enum fields defined.
    pub fn parse_enum_def(&self) -> ParseResult<EnumDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Enum)));

        let mut gen = self.parse_delim_tree(
            Delimiter::Paren,
            Some(ParseErrorKind::TypeDefinition(TyArgumentKind::Enum)),
        )?;

        let entries = gen.parse_separated_fn(
            |g| g.parse_enum_def_entry(),
            |g| g.parse_token(TokenKind::Comma),
        )?;

        Ok(EnumDef { entries })
    }

    /// Parse an [EnumDefEntry].
    pub fn parse_enum_def_entry(&self) -> ParseResult<AstNode<EnumDefEntry>> {
        let name = self.parse_name()?;
        let name_span = name.span();

        let mut args = AstNodes::empty();

        if matches!(self.peek(), Some(token) if token.is_paren_tree()) {
            let mut gen = self.parse_delim_tree(Delimiter::Paren, None)?;
            args =
                gen.parse_separated_fn(|g| g.parse_type(), |g| g.parse_token(TokenKind::Comma))?;
        }

        Ok(self.node_with_joined_span(EnumDefEntry { name, args }, name_span))
    }

    /// Parse a [TyFnDef]. Type functions specify logic at the type
    /// level on expressions such as struct, enum, function, and trait
    /// definitions.
    pub fn parse_ty_fn_def(&mut self) -> ParseResult<TyFnDef> {
        let mut params = AstNodes::empty();

        // Flag denoting that we were able to parse the ending `>` within the function
        // def arg
        let mut arg_ending = false;

        while let Some(param) = self.peek_resultant_fn(|g| g.parse_ty_fn_def_arg()) {
            params.nodes.push(param);

            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Comma) => {
                    self.skip_token();
                }
                Some(token) if token.has_kind(TokenKind::Gt) => {
                    self.skip_token();
                    arg_ending = true;
                    break;
                }
                token => self.error_with_location(
                    ParseErrorKind::Expected,
                    Some(TokenKindVector::from_vec(smallvec![TokenKind::Comma, TokenKind::Gt])),
                    token.map(|t| t.kind),
                    token.map_or_else(|| self.next_location(), |t| t.span),
                )?,
            }
        }

        // So if we failed to parse even a `>` we should report this...
        if !arg_ending {
            self.error_with_location(
                ParseErrorKind::Expected,
                Some(TokenKindVector::singleton(TokenKind::Gt)),
                self.peek().map(|tok| tok.kind),
                self.next_location(),
            )?;
        }

        // see if we need to add a return ty...
        let return_ty = match self.peek_resultant_fn(|g| g.parse_thin_arrow()) {
            Some(_) => Some(self.parse_type()?),
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
    fn parse_ty_fn_def_arg(&self) -> ParseResult<AstNode<Param>> {
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

        Ok(self.node_with_joined_span(
            Param {
                name,
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
    pub fn parse_trait_def(&self) -> ParseResult<TraitDef> {
        debug_assert!(self.current_token().has_kind(TokenKind::Keyword(Keyword::Trait)));

        Ok(TraitDef { members: self.parse_exprs_from_braces()? })
    }
}
