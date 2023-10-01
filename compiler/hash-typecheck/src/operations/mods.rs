use hash_reporting::diagnostic::ErrorState;
use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    context::HasContext,
    tir::{ModDefId, ModMemberId, ModMemberValue, NodeId, Term, Ty},
};

use crate::{
    env::TcEnv,
    tc::{FnInferMode, Tc},
    traits::{Operations, OperationsOnNode},
    utils::dumping::potentially_dump_tir,
};

impl<E: TcEnv> OperationsOnNode<ModDefId> for Tc<'_, E> {
    type TyNode = ();

    fn check_node(&self, mod_def_id: ModDefId, _: ()) -> crate::errors::TcResult<()> {
        self.context().enter_scope(mod_def_id.into(), || {
            let members = mod_def_id.borrow().members;
            let mut error_state = ErrorState::new();

            // Infer each member signature
            for member in members.value().iter() {
                let _ = error_state.try_or_add_error(self.check_node(member, ()));
            }

            error_state.into_error(|| Ok(()))
        })
    }

    fn normalise_node(
        &self,
        _item: ModDefId,
    ) -> crate::options::normalisation::NormaliseResult<ModDefId> {
        todo!()
    }

    fn unify_nodes(&self, _src: ModDefId, _target: ModDefId) -> crate::errors::TcResult<()> {
        todo!()
    }
}

impl<E: TcEnv> OperationsOnNode<ModMemberId> for Tc<'_, E> {
    type TyNode = ();

    fn check_node(&self, mod_member: ModMemberId, _: Self::TyNode) -> crate::errors::TcResult<()> {
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
                    Ty::hole(fn_def_id.origin().inferred()),
                    Term::hole(fn_def_id.origin()),
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

    fn normalise_node(
        &self,
        _item: ModMemberId,
    ) -> crate::options::normalisation::NormaliseResult<ModMemberId> {
        todo!()
    }

    fn unify_nodes(&self, _src: ModMemberId, _target: ModMemberId) -> crate::errors::TcResult<()> {
        todo!()
    }
}
