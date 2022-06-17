use std::collections::HashSet;

use hash_ast::{
    ast::{AstNodes, BodyBlock, Expression, ExpressionKind},
    visitor::AstVisitor,
};

use crate::visitor::SemanticAnalysisContext;

use super::{
    error::{AnalysisErrorKind, BlockOrigin},
    SemanticAnalyser,
};

impl SemanticAnalyser {
    /// This function will verify that all of the given expressions are declarations.
    /// During the checking process, the function also collects the indices of
    /// the erroneous statements in the provided [AstNodes<Expression>]. This is
    /// so that the caller can later 'skip' these statements when performing further checks.
    pub(crate) fn check_statements_are_declarative(
        &mut self,
        ctx: &SemanticAnalysisContext,
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
                    ctx.source_id,
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
    pub(crate) fn check_constant_body_block(
        &mut self,
        ctx: &SemanticAnalysisContext,
        body: &BodyBlock,
        origin: BlockOrigin,
    ) {
        assert!(body.expr.is_none());

        let errors = self.check_statements_are_declarative(ctx, &body.statements, origin);

        // We have to manually walk this block because we want to skip any erroneous
        // statements.
        for (index, statement) in body.statements.iter().enumerate() {
            if errors.contains(&index) {
                self.visit_expression(ctx, statement.ast_ref()).unwrap();
            }
        }
    }
}
