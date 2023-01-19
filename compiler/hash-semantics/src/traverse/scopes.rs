//! Typechecking traversal for constant scopes. This includes modules, mod/impl
//! blocks, trait blocks.

use hash_ast::{ast, visitor::AstVisitor};
use hash_source::identifier::Identifier;
use hash_tir::scope::{ScopeId, ScopeKind};

use super::visitor::TcVisitor;
use crate::{diagnostics::error::TcResult, ops::AccessToOps};

pub(crate) struct VisitConstantScope {
    pub(crate) scope_name: Option<Identifier>,
    pub(crate) scope_id: ScopeId,
}

impl<'tc> TcVisitor<'tc> {
    /// Visit a constant scope, creating a [ScopeId] corresponding to it, and a
    /// derived name from a parent declaration.
    ///
    /// The `scope_to_use` parameter is optional and is used to override the
    /// scope that is used to append all the members into. If not given, a new
    /// constant scope is created and used.
    pub(crate) fn visit_constant_scope<'m, T>(
        &self,
        members: impl Iterator<Item = ast::AstNodeRef<'m, ast::Expr>>,
        originating_node: ast::AstNodeRef<T>,
        scope_to_use: Option<ScopeId>,
        scope_kind: ScopeKind,
    ) -> TcResult<VisitConstantScope> {
        // Create a scope and enter it, for adding all the members:
        let scope_id = scope_to_use.unwrap_or_else(|| self.builder().create_scope(scope_kind, []));

        // Get the name of the scope from the surrounding declaration hint, if any.
        // This is only useful for mod/impl/trait blocks
        let scope_name = self.state.declaration_name_hint.take();

        self.scope_manager().enter_scope(scope_id, |_| {
            // @@Todo: deal with recursive declarations

            // Invariant: It is already checked during semantics that only declarations are
            // present in constant scopes.
            for member in members {
                self.visit_expr(member)?;
            }
            Ok(())
        })?;

        // Assign the scope to the target node
        self.register_node_info(originating_node, scope_id);

        Ok(VisitConstantScope { scope_name, scope_id })
    }
}