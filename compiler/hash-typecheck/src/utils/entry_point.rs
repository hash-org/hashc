//! Functionality relating to finding the entry point of a program.
use hash_attrs::{attr::attr_store, builtin::attrs};
use hash_source::{entry_point::EntryPointKind, identifier::IDENTS, ModuleKind};
use hash_storage::store::statics::{SequenceStoreValue, StoreId};
use hash_tir::tir::{
    Arg, CallTerm, FnDefId, FnTy, HasAstNodeId, Node, NodeId, NodeOrigin, Param, Term, Ty,
};

use crate::{diagnostics::TcResult, env::TcEnv, tc::Tc, traits::OperationsOnNode};

impl<T: TcEnv> Tc<'_, T> {
    /// Flag the given function as an entry point if it is one.
    ///
    /// This is done by checking if the function is named "main" or if it has
    /// the #entry_point directive.
    pub fn potentially_flag_fn_as_entry_point(&self, fn_def_id: FnDefId) -> TcResult<()> {
        if self.entry_point().has() {
            return Ok(());
        }

        let fn_def_symbol = fn_def_id.borrow().name;
        let fn_def_name = fn_def_symbol.borrow().name.unwrap();
        let fn_def_ty = fn_def_id.borrow().ty;

        // Check if on item if it has `entry_point`
        let has_entry_point_attr =
            attr_store().node_has_attr(fn_def_id.node_id_or_default(), attrs::ENTRY_POINT);

        let kind = self.current_source().module_kind();

        let entry_point = if has_entry_point_attr {
            Some(EntryPointKind::Named(fn_def_name))
        } else if fn_def_name == IDENTS.main && kind == Some(ModuleKind::EntryPoint) {
            Some(EntryPointKind::Main)
        } else {
            None
        };

        if let Some(entry_point) = entry_point {
            let expected_ty = Node::create_at(
                Ty::FnTy(FnTy {
                    implicit: false,
                    is_unsafe: false,
                    params: Param::seq_positional([], NodeOrigin::Expected),
                    pure: false,
                    return_ty: Term::unit_ty(NodeOrigin::Expected),
                }),
                NodeOrigin::Expected,
            );

            self.unify_nodes(Node::create_at(Ty::FnTy(fn_def_ty), fn_def_id.origin()), expected_ty)?;

            // If successful, flag it as an entry point.
            self.entry_point().set(fn_def_id, entry_point);
        }

        Ok(())
    }
}
