//! Hash semantic analysis module for validating various constructs relating to
//! blocks within the AST.

use std::{collections::HashSet, mem};

use hash_ast::{
    ast::{AstNodeRef, BodyBlock, Expr, ExprKind},
    visitor::AstVisitor,
};

use super::SemanticAnalyser;
use crate::diagnostics::{error::AnalysisErrorKind, origins::BlockOrigin};

impl SemanticAnalyser<'_> {
    /// This function will verify that all of the given expressions are
    /// declarations. Additionally, the function checks that all of the
    /// declarations within the scope do not attempt to declare the binding
    /// to be `mutable` as this is disallowed.
    ///
    /// During the checking process, the function also collects the indices of
    /// the erroneous statements in the provided [AstNodes<Expression>]. This is
    /// so that the caller can later 'skip' these statements when performing
    /// further checks.
    pub(crate) fn check_members_are_declarative<'s>(
        &mut self,
        members: impl Iterator<Item = AstNodeRef<'s, Expr>>,
        origin: BlockOrigin,
    ) -> HashSet<usize> {
        let mut error_indices = HashSet::new();

        for (index, statement) in members.enumerate() {
            if !matches!(statement.kind(), ExprKind::Declaration(_) | ExprKind::MergeDeclaration(_))
            {
                self.append_error(
                    AnalysisErrorKind::NonDeclarativeExpression { origin },
                    statement.span(),
                );

                error_indices.insert(index);
            }
        }

        error_indices
    }

    /// This function is used that a given 'constant' block adheres to the
    /// specified semantic rules:
    ///
    /// - All members must be only declarative
    ///
    /// - No member can declare themselves to be `mutable`
    pub(crate) fn check_constant_body_block(&mut self, body: &BodyBlock, origin: BlockOrigin) {
        let errors = self.check_members_are_declarative(body.members(), origin);

        // We need to set the block to being whatever the origin is set to!
        let old_block_origin = mem::replace(&mut self.current_block, origin);

        // We have to manually walk this block because we want to skip any erroneous
        // statements.
        for (index, statement) in body.statements.iter().enumerate() {
            if errors.contains(&index) {
                self.visit_expr(&(), statement.ast_ref()).unwrap();
            }
        }

        self.current_block = old_block_origin;
    }
}
