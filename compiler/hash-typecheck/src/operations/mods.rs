use std::ops::ControlFlow;

use hash_reporting::diagnostic::ErrorState;
use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    context::HasContext,
    tir::{ModDefId, ModMemberId, ModMemberValue, NodeId, Term},
    visitor::{Atom, Map, Visit},
};

use crate::{
    diagnostics::{TcError, TcResult},
    env::TcEnv,
    options::normalisation::{already_normalised, NormaliseResult},
    tc::{FnInferMode, Tc},
    traits::{OperationsOn, OperationsOnNode},
    utils::dumping::potentially_dump_tir,
};

impl<E: TcEnv> OperationsOnNode<ModDefId> for Tc<'_, E> {
    type AnnotNode = ();

    fn check_node(&self, mod_def_id: ModDefId, _: ()) -> TcResult<()> {
        self.context().enter_scope(mod_def_id.into(), || -> TcResult<()> {
            let members = mod_def_id.borrow().members;

            // Infer each member signature
            for member in members.value().iter() {
                self.check_node(member, ())?;
            }

            Ok(())
        })?;

        self.visitor().visit(mod_def_id, &mut |atom| match atom {
            Atom::Term(term) => {
                term.set(self.resolve_metas_and_vars(term).0.value());
                ControlFlow::Continue(())
            }
            Atom::FnDef(_) => ControlFlow::Continue(()),
            Atom::Lit(_) => ControlFlow::Break(()),
        });

        Ok(())
    }

    fn try_normalise_node(&self, _item: ModDefId) -> NormaliseResult<ControlFlow<ModDefId>> {
        already_normalised()
    }

    fn unify_nodes(&self, src: ModDefId, target: ModDefId) -> TcResult<()> {
        if src == target {
            Ok(())
        } else {
            Err(TcError::MismatchingModDefs { expected: target, actual: src })
        }
    }
}

impl<E: TcEnv> OperationsOnNode<ModMemberId> for Tc<'_, E> {
    type AnnotNode = ();

    fn check_node(&self, mod_member: ModMemberId, _: Self::AnnotNode) -> TcResult<()> {
        let value = mod_member.borrow().value;
        match value {
            ModMemberValue::Data(data_def_id) => {
                self.check_node(data_def_id, ())?;
                Ok(())
            }
            ModMemberValue::Mod(mod_def_id) => {
                self.check_node(mod_def_id, ())?;
                Ok(())
            }
            ModMemberValue::Fn(fn_def_id) => {
                let mut id = fn_def_id;
                self.check(
                    &mut id,
                    self.fresh_meta_for(fn_def_id),
                    Term::from(fn_def_id, fn_def_id.origin()),
                )?;
                if self.fn_infer_mode.get() == FnInferMode::Body {
                    // Dump TIR if necessary
                    potentially_dump_tir(fn_def_id);

                    // Check for entry point
                    self.potentially_flag_fn_as_entry_point(fn_def_id)?;
                }
                Ok(())
            }
            ModMemberValue::Intrinsic(_) => {
                // Nothing to do
                Ok(())
            }
        }
    }

    fn try_normalise_node(&self, _item: ModMemberId) -> NormaliseResult<ControlFlow<ModMemberId>> {
        already_normalised()
    }

    fn unify_nodes(&self, _: ModMemberId, _: ModMemberId) -> TcResult<()> {
        // Not needed
        unreachable!()
    }
}
