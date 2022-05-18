//! Hash compiler AST generation sources. This file contains the sources to the logic
//! that transforms tokens into an AST.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use hash_ast::ast::*;
use hash_token::TokenKind;

use super::{error::AstGenErrorKind, AstGen, AstGenResult};

impl<'c, 'stream, 'resolver> AstGen<'c, 'stream, 'resolver> {
    /// Parse a subset of the [Statement] variants which don't include definitions of
    /// structs, enums, or traits. This function deals with attempting to parse declarations
    /// or expressions that are terminated with a semi-colon.
    pub fn parse_statement(
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

                    Some(Statement::Expr(ExprStatement(self.node_with_span(
                        Expression::new(ExpressionKind::Declaration(decl)),
                        start,
                    ))))
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
                        Some(token) => {
                            self.error(AstGenErrorKind::ExpectedExpression, None, Some(token.kind))
                        }
                        // Special case where there is a expression at the end of the stream and therefore it
                        // is signifying that it is returning the expression value here
                        None => Ok(Statement::Expr(ExprStatement(expr))),
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
            self.node_with_span(statement, start.join(location)),
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
        // debug_assert!(self
        //     .current_token()
        //     .has_kind(TokenKind::Keyword(Keyword::Trait)));

        // let name = self.parse_name()?;

        // self.parse_token_atom(TokenKind::Eq)?;
        // let bound = self.parse_type_bound()?;

        // self.parse_arrow()?; // the next token should be a TokenTree delimited with an arrow.

        // let trait_type = self.parse_function_or_tuple_type(true)?;

        // Ok(TraitDef {
        //     name,
        //     bound,
        //     trait_type,
        // })
        todo!()
    }
}
