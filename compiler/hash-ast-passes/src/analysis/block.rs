use std::{collections::HashSet, mem};

use hash_ast::{
    ast::{AstNodes, BodyBlock, Expression, ExpressionKind},
    visitor::AstVisitor,
};

use super::{
    error::{AnalysisErrorKind, BlockOrigin},
    SemanticAnalyser,
};

impl SemanticAnalyser {
    /// This function will verify that all of the given expressions are declarations. Additionally,
    /// the function checks that all of the declarations within the scope do not attempt to
    /// declare the binding to be `mutable` as this is disallowed.
    ///
    /// During the checking process, the function also collects the indices of
    /// the erroneous statements in the provided [AstNodes<Expression>]. This is
    /// so that the caller can later 'skip' these statements when performing further checks.
    pub(crate) fn check_statements_are_declarative(
        &mut self,
        statements: &AstNodes<Expression>,
        origin: BlockOrigin,
    ) -> HashSet<usize> {
        let mut error_indices = HashSet::new();

        for (index, statement) in statements.iter().enumerate() {
            if !matches!(
                statement.kind(),
                ExpressionKind::Declaration(_) | ExpressionKind::MergeDeclaration(_)
            ) {
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
        assert!(body.expr.is_none());

        let errors = self.check_statements_are_declarative(&body.statements, origin);

        // We need to set the block to being whatever the origin is set to!
        let old_block_origin = mem::replace(&mut self.current_block, origin);

        // We have to manually walk this block because we want to skip any erroneous
        // statements.
        for (index, statement) in body.statements.iter().enumerate() {
            if errors.contains(&index) {
                self.visit_expression(&(), statement.ast_ref()).unwrap();
            }
        }

        self.current_block = old_block_origin;
    }
}
