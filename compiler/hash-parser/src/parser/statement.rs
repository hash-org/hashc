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
    /// Parse a [Statement] which includes all variants of any statement
    /// within the language. This function is eager and does not assume that
    /// the result might produce an [Expression] that is not terminated by a
    /// semi-colon.
    pub fn parse_statement(&self) -> AstGenResult<'c, AstNode<'c, Statement<'c>>> {
        let start = self.current_location();

        match self.peek() {
            Some(Token { kind, span: _ }) if kind.begins_statement() => {
                self.skip_token();

                let statement = match kind {
                    TokenKind::Keyword(Keyword::Trait) => {
                        Statement::TraitDef(self.parse_trait_defn()?)
                    }
                    TokenKind::Keyword(Keyword::Enum) => {
                        Statement::EnumDef(self.parse_enum_defn()?)
                    }
                    TokenKind::Keyword(Keyword::Struct) => {
                        Statement::StructDef(self.parse_struct_defn()?)
                    }
                    TokenKind::Keyword(Keyword::Continue) => Statement::Continue(ContinueStatement),
                    TokenKind::Keyword(Keyword::Break) => Statement::Break(BreakStatement),
                    TokenKind::Keyword(Keyword::Return) => {
                        // @@Hack: check if the next token is a semi-colon, if so the return statement
                        // has no returned expression...
                        match self.peek() {
                            Some(token) if token.has_kind(TokenKind::Semi) => {
                                Statement::Return(ReturnStatement(None))
                            }
                            Some(_) => Statement::Return(ReturnStatement(Some(
                                self.parse_expression_with_precedence(0)?,
                            ))),
                            None => Statement::Return(ReturnStatement(None)),
                        }
                    }
                    _ => unreachable!(),
                };

                let current_location = self.current_location();

                match self.next_token() {
                    Some(token) if token.has_kind(TokenKind::Semi) => {
                        Ok(self.node_with_location(statement, start.join(current_location)))
                    }
                    Some(token) => self.error_with_location(
                        AstGenErrorKind::ExpectedExpression,
                        None,
                        Some(token.kind),
                        current_location,
                    ),
                    None => self.error(AstGenErrorKind::EOF, None, Some(*kind))?,
                }
            }
            Some(_) => self
                .parse_general_statement(true) // This probably shouldn't be a 1?
                .map(|statement| statement.1),
            None => self.error(AstGenErrorKind::ExpectedStatement, None, None)?,
        }
    }

    /// Parse a subset of the [Statement] variants which don't include definitions of
    /// structs, enums, or traits. This function deals with attempting to parse declarations
    /// or expressions that are terminated with a semi-colon.
    pub fn parse_general_statement(
        &self,
        semi_required: bool,
    ) -> AstGenResult<'c, (bool, AstNode<'c, Statement<'c>>)> {
        let start = self.current_location();
        let offset = self.offset();

        let decl = if let Some(pat) = self.peek_resultant_fn(|| self.parse_singular_pattern()) {
            // Check if there is a colon here and if not we have to backtrack and
            // now attempt to parse a simple expression

            match self.peek() {
                Some(token) if token.has_kind(TokenKind::Colon) => {
                    let decl = self.parse_declaration(pat)?;

                    Some(Statement::Expr(ExprStatement(self.node_with_location(
                        Expression::new(ExpressionKind::Declaration(decl)),
                        start,
                    ))))
                }
                Some(token) if token.has_kind(TokenKind::Lt) => {
                    // Here we essentially have to pre-emptively assume that the parsing the
                    // type arguments might simply be a top level expression and therefore
                    // if parsing this fails, then we have to backtrack
                    match self.parse_declaration(pat) {
                        Ok(decl) => Some(Statement::Expr(ExprStatement(self.node_with_location(
                            Expression::new(ExpressionKind::Declaration(decl)),
                            start,
                        )))),
                        Err(_) => {
                            self.offset.set(offset);
                            None
                        }
                    }
                }
                _ => {
                    self.offset.set(offset);
                    None
                }
            }
        } else {
            None
        };

        let statement = match decl {
            Some(statement) => Ok(statement),
            None => {
                let (expr, re_assigned) = self.try_parse_expression_with_re_assignment()?;

                if re_assigned {
                    Ok(Statement::Expr(ExprStatement(expr)))
                } else {
                    match self.peek() {
                        Some(token) if token.has_kind(TokenKind::Semi) => {
                            // We don't skip here because it is handled after the statement has been generated.
                            Ok(Statement::Expr(ExprStatement(expr)))
                        }
                        Some(token) if token.has_kind(TokenKind::Eq) => {
                            self.skip_token();

                            // Parse the rhs and the semi
                            let rhs = self.parse_expression_with_precedence(0)?;

                            Ok(Statement::Assign(AssignStatement { lhs: expr, rhs }))
                        }

                        // Special case where there is a expression at the end of the stream and therefore it
                        // is signifying that it is returning the expression value here
                        None => Ok(Statement::Expr(ExprStatement(expr))),

                        token => match (token, expr.into_body().move_out().into_kind()) {
                            (_, ExpressionKind::Block(BlockExpr(block))) => {
                                Ok(Statement::Block(BlockStatement(block)))
                            }
                            (Some(token), _) => self.error(
                                AstGenErrorKind::ExpectedExpression,
                                None,
                                Some(token.kind),
                            ),
                            (None, _) => unreachable!(),
                        },
                    }
                }
            }
        }?;

        let location = self.current_location();

        // Depending on whether it's expected of the expression to have a semi-colon, we
        // try and parse one anyway, if so
        let has_semi = if semi_required {
            self.parse_token_atom(TokenKind::Semi)?;
            true
        } else {
            self.parse_token_atom_fast(TokenKind::Semi).is_some()
        };

        Ok((
            has_semi,
            self.node_with_location(statement, start.join(location)),
        ))
    }

    /// Parse a trait definition. AST representation of a trait statement.
    /// A trait statement is essentially a function with no body, with a
    /// for-all node and some genetic type arguments. For example,
    ///
    /// trait eq<T> => (T, T) => bool;
    ///     ┌─^^ ^─┐   ^─ ─ ─ ─ ─ ─ ─ ┐
    ///   name   Generic type args    Function type definition
    pub fn parse_trait_defn(&self) -> AstGenResult<'c, TraitDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Trait)));

        let name = self.parse_name()?;

        self.parse_token_atom(TokenKind::Eq)?;
        let bound = self.parse_type_bound()?;

        self.parse_arrow()?; // the next token should be a TokenTree delimited with an arrow.

        let trait_type = self.parse_function_or_tuple_type(true)?;

        Ok(TraitDef {
            name,
            bound,
            trait_type,
        })
    }

    /// AST representation of a struct which includes the name of the struct with a
    /// ForAll to specify any bounds or and generic arguments to the struct, with
    /// zero or more struct fields. An example for a struct would be:
    ///
    /// struct Name <T,Q> where eq<T> { ... };
    ///        ^^^^    ^──────^^─┬──^   ^^^
    /// Name of struct        For all  fields
    pub fn parse_struct_defn(&self) -> AstGenResult<'c, StructDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Struct)));

        let name = self.parse_name()?;
        self.parse_token_atom(TokenKind::Eq)?;

        let (bound, entries) = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Lt) => {
                let bound = Some(self.parse_type_bound()?);
                self.parse_arrow()?;
                let entries = self.parse_struct_def_entries()?;

                (bound, entries)
            }

            Some(token) if token.is_brace_tree() => {
                let entries = self.parse_struct_def_entries()?;

                (None, entries)
            }
            token => self.error(
                AstGenErrorKind::TyArgument(TyArgumentKind::Struct),
                None,
                token.map(|tok| tok.kind),
            )?,
        };

        Ok(StructDef {
            name,
            bound,
            entries,
        })
    }

    /// Parse an enum definition. AST representation for an enum, An enum is constructed by
    /// a the keyword 'enum' followed by an identifier name, a for-all declaration,
    /// followed by some enum fields. An enumeration can be made of zero or more enum fields.
    /// For example, a declaration of an enum would be:
    ///
    /// enum Name<T,Q> where eq<T> => { ... };
    ///      ^^^^  ^──────^^─┬──^       ^^^
    /// Name of enum      For all      fields
    ///
    pub fn parse_enum_defn(&self) -> AstGenResult<'c, EnumDef<'c>> {
        debug_assert!(self
            .current_token()
            .has_kind(TokenKind::Keyword(Keyword::Enum)));

        let name = self.parse_name()?;

        self.parse_token_atom(TokenKind::Eq)?;

        // now parse the optional type bound and the enum definition entries,
        // if a type bound is specified, then the definition of the struct should
        // be followed by an arrow ('=>')...
        let (bound, entries) = match self.peek() {
            Some(token) if token.has_kind(TokenKind::Lt) => {
                let bound = Some(self.parse_type_bound()?);
                self.parse_arrow()?;

                let entries = self.parse_enum_def_entries()?;

                (bound, entries)
            }

            Some(token) if token.is_brace_tree() => {
                let entries = self.parse_enum_def_entries()?;

                (None, entries)
            }
            token => self.error(
                AstGenErrorKind::TyArgument(TyArgumentKind::Enum),
                None,
                token.map(|tok| tok.kind),
            )?,
        };

        Ok(EnumDef {
            name,
            bound,
            entries,
        })
    }

    /// Function used to pass a comma separated [EnumDefEntry] which is proceeded
    /// within the beginning of an [EnumDef].
    pub fn parse_enum_def_entries(&self) -> AstGenResult<'c, AstNodes<'c, EnumDefEntry<'c>>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            }) => {
                self.skip_token();
                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, *span);

                gen.parse_separated_fn(
                    || gen.parse_enum_def_entry(),
                    || gen.parse_token_atom(TokenKind::Comma),
                )
            }
            Some(token) => self.error(
                AstGenErrorKind::Expected,
                Some(TokenKindVector::singleton(
                    &self.wall,
                    TokenKind::Delimiter(Delimiter::Brace, false),
                )),
                Some(token.kind),
            ),
            None => self.unexpected_eof(),
        }
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

        Ok(self.node_with_joined_location(EnumDefEntry { name, args }, &name_location))
    }

    /// Function used to pass a comma separated [StructDefEntry] which is proceeded
    /// within the beginning of an [StructDef].
    pub fn parse_struct_def_entries(&self) -> AstGenResult<'c, AstNodes<'c, StructDefEntry<'c>>> {
        match self.peek() {
            Some(Token {
                kind: TokenKind::Tree(Delimiter::Brace, tree_index),
                span,
            }) => {
                self.skip_token();

                let tree = self.token_trees.get(*tree_index).unwrap();
                let gen = self.from_stream(tree, *span);

                gen.parse_separated_fn(
                    || gen.parse_struct_def_entry(),
                    || gen.parse_token_atom(TokenKind::Comma),
                )
            }
            Some(token) => {
                let atom = token.kind;
                let expected = TokenKindVector::from_row(
                    row![&self.wall; TokenKind::Delimiter(Delimiter::Brace, true)],
                );

                self.error(AstGenErrorKind::Expected, Some(expected), Some(atom))?
            }
            None => self.unexpected_eof(),
        }
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

        Ok(self.node_with_joined_location(StructDefEntry { name, ty, default }, &start))
    }
}
