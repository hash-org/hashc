// @@Docs
use derive_more::Constructor;
use hash_types::new::{
    environment::env::AccessToEnv,
    refs::RefTy,
    terms::{Term, TermId},
    tys::{Ty, TyId},
};
use hash_utils::store::{CloneStore, Store};

use super::common_ops::CommonOps;
use crate::{
    impl_access_to_tc_env,
    new::{
        diagnostics::{
            error::{TcError, TcResult},
            panic::tc_panic_on_many,
        },
        environment::tc_env::TcEnv,
    },
};

#[derive(Constructor)]
pub struct InferOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(InferOps<'tc>);

impl<'tc> InferOps<'tc> {
    /**
     * Infer the type of a term, or create a new a type hole.
     */
    pub fn infer_ty_of_term_or_hole(&self, term: TermId) -> TyId {
        self.infer_ty_of_term(term).unwrap_or_else(|_| self.new_ty_hole())
    }

    /// Infer a concrete type for a given term.
    ///
    /// If this is not possible, return `None`.
    /// To create a hole when this is not possible, use
    /// [`InferOps::infer_ty_of_term_or_hole`].
    pub fn infer_ty_of_term(&self, term: TermId) -> TcResult<TyId> {
        match self.stores().term().get(term) {
            Term::Runtime(rt_term) => Ok(rt_term.term_ty),
            Term::Tuple(_) => todo!(),
            Term::Lit(_) => todo!(),
            Term::Ctor(_) => {
                todo!()
            }
            Term::FnCall(_) => todo!(),
            Term::Closure(fn_def_id) => Ok(self
                .stores()
                .fn_def()
                .map_fast(fn_def_id, |fn_def| self.new_ty(Ty::Fn(fn_def.ty)))),
            Term::Block(_) => todo!(),
            Term::Var(_) => todo!(),
            Term::Loop(_) => {
                // @@Future: if loop is proven to not break, return never
                Ok(self.new_void_ty())
            }
            Term::LoopControl(_) => todo!(),
            Term::Match(_) => todo!(),
            Term::Return(_) => todo!(),
            Term::DeclStackMember(_) => todo!(),
            Term::Assign(_) => todo!(),
            Term::Unsafe(_) => todo!(),
            Term::Access(_) => todo!(),
            Term::Cast(_) => todo!(),
            Term::TypeOf(_) => todo!(),
            Term::Ty(ty_id) => {
                match self.get_ty(ty_id) {
                    Ty::Hole(_) => Err(TcError::NeedMoreTypeAnnotationsToInfer { term }),
                    Ty::Tuple(_) | Ty::Fn(_) | Ty::Ref(_) | Ty::Data(_) => {
                        // @@Todo: bounds
                        Ok(self.new_small_universe_ty())
                    }
                    Ty::Universe(universe_ty) => Ok(self.new_universe_ty(universe_ty.size + 1)),
                    Ty::Var(_) => todo!(),
                    Ty::Eval(_) => todo!(),
                }
            }
            Term::Ref(ref_term) => {
                let inner_ty = self.infer_ty_of_term_or_hole(ref_term.subject);
                Ok(self.new_ty(Ty::Ref(RefTy {
                    ty: inner_ty,
                    mutable: ref_term.mutable,
                    kind: ref_term.kind,
                })))
            }
            Term::Deref(_) => todo!(),
            Term::Hole(_) => {
                tc_panic_on_many!([term, term], self, "What")
            }
        }
    }
}
