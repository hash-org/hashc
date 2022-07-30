//! Typechecking traversal for constant scopes. This includes modules, mod/impl
//! blocks, trait blocks.

use super::TcVisitor;
use crate::{
    diagnostics::error::TcResult,
    ops::{scope::ScopeManager, AccessToOpsMut},
    storage::primitives::{ScopeId, ScopeKind},
};
use hash_ast::{ast, visitor::AstVisitor};
use hash_source::identifier::Identifier;

pub(crate) struct VisitConstantScope {
    pub(crate) scope_name: Option<Identifier>,
    pub(crate) scope_id: ScopeId,
}

impl<'gs, 'ls, 'cd, 'src> TcVisitor<'gs, 'ls, 'cd, 'src> {
    /// Visit a constant scope, creating a [ScopeId] corresponding to it, and a
    /// derived name from a parent declaration.
    ///
    /// The `scope_to_use` parameter is optional and is used to override the
    /// scope that is used to append all the members into. If not given, a new
    /// constant scope is created and used.
    pub(crate) fn visit_constant_scope<'m>(
        &mut self,
        ctx: &<Self as AstVisitor>::Ctx,
        members: impl Iterator<Item = ast::AstNodeRef<'m, ast::Expr>>,
        scope_to_use: Option<ScopeId>,
    ) -> TcResult<VisitConstantScope> {
        // Create a scope and enter it, for adding all the members:
        let scope_id =
            scope_to_use.unwrap_or_else(|| self.builder().create_scope(ScopeKind::Constant, []));

        ScopeManager::enter_scope_with(self, scope_id, |this| {
            // @@Todo: deal with recursive declarations

            // Invariant: It is already checked during semantics that only declarations are
            // present in constant scopes.
            for (i, member) in members.enumerate() {
                this.visit_expr(ctx, member)?;

                // Add location to the declaration
                this.copy_location_from_node_to_target(member, (scope_id, i));
            }
            Ok(())
        })?;

        // Get the name of the scope from the surrounding declaration hint, if any.
        // This is only useful for mod/impl/trait blocks
        let scope_name = self.state.declaration_name_hint.take();

        Ok(VisitConstantScope { scope_name, scope_id })
    }
}
