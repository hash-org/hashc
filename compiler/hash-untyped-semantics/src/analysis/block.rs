//! Hash semantic analysis module for validating various constructs relating to
//! blocks within the AST.

use std::{cell::Cell, collections::HashSet, mem};

use hash_ast::{
    ast::{self, AstNodeRef, Block, BlockExpr, Expr, ExprMacroInvocation},
    origin::BlockOrigin,
    visitor::AstVisitorMutSelf,
};

use super::SemanticAnalyser;
use crate::diagnostics::error::AnalysisErrorKind;

impl SemanticAnalyser {
    /// This function will verify that all of the given expressions are
    /// declarations. Additionally, the function checks that all of the
    /// declarations within the scope do not attempt to declare the binding
    /// to be `mutable` as this is disallowed.
    ///
    /// During the checking process, the function also collects the indices of
    /// the erroneous statements in the provided
    /// [hash_ast::ast::AstNodes<Expression>]. This is so that the caller can
    /// later 'skip' these statements when performing further checks.
    pub(crate) fn check_members_are_declarative<'a>(
        &mut self,
        members: impl Iterator<Item = ast::AstNodeRef<'a, ast::Expr>>,
        origin: BlockOrigin,
    ) -> HashSet<usize> {
        let mut error_indices = HashSet::new();

        let allowed_top_level_expr =
            |statement: AstNodeRef<Expr>| matches!(statement.body(), Expr::Declaration(_));

        for (index, statement) in members.enumerate() {
            let current = Cell::new(statement);

            let mut emit_err = |this: &mut Self| {
                this.append_error(
                    AnalysisErrorKind::NonDeclarativeExpression { origin },
                    statement,
                );
                error_indices.insert(index);
            };

            // Since directives are allowed at the level because they apply onto
            // the child declaration, we actually need to check the child of the
            // directive, not the directive itself.
            loop {
                let current_value = current.get();
                match current_value.body {
                    Expr::Macro(ExprMacroInvocation { subject, .. }) => {
                        current.set(subject.ast_ref());
                    }
                    Expr::Block(BlockExpr { data }) => {
                        match data.ast_ref().body {
                            Block::Body(body) => {
                                // Don't append any of the indices of the body block, but make
                                // sure that all members of the body block adhere to the same
                                // rules...
                                let indices =
                                    self.check_members_are_declarative(body.members(), origin);

                                // If there were problems within the inner body block, then we
                                // report that the entire block is
                                // invalid.
                                if !indices.is_empty() {
                                    emit_err(self)
                                }
                            }
                            _ => emit_err(self),
                        }

                        break;
                    }
                    _ => {
                        if !allowed_top_level_expr(current_value) {
                            emit_err(self);
                        }
                        break;
                    }
                }
            }
        }

        error_indices
    }

    /// This function is used to check that members of a block scope adhere to
    /// specified semantic rules:
    ///
    /// - All members must be only declarative
    ///
    /// - No member can declare themselves to be `mutable`
    pub(crate) fn check_constant_scope_members(
        &mut self,
        members: &ast::AstNodes<Expr>,
        origin: BlockOrigin,
    ) {
        let errors = self.check_members_are_declarative(members.ast_ref_iter(), origin);

        // We need to set the block to being whatever the origin is set to!
        let old_block_origin = mem::replace(&mut self.current_block, origin);

        // We have to manually walk this block because we want to skip any erroneous
        // statements.
        for (index, statement) in members.iter().enumerate() {
            if errors.contains(&index) {
                self.visit_expr(statement.ast_ref()).unwrap();
            }
        }

        self.current_block = old_block_origin;
    }
}
