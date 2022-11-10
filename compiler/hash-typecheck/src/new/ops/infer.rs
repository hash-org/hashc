// @@Docs
use derive_more::Constructor;
use hash_types::new::{
    environment::env::AccessToEnv,
    refs::RefTy,
    terms::{Term, TermId},
    tys::{Ty, TyId},
};
use hash_utils::store::{CloneStore, Store};

use super::{common::CommonOps, AccessToOps};
use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

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
        self.infer_ty_of_term(term).unwrap_or_else(|| self.new_ty_hole())
    }

    /// Infer a concrete type for a given term.
    ///
    /// If this is not possible, return `None`.
    /// To create a hole when this is not possible, use
    /// [`InferOps::infer_ty_of_term_or_hole`].
    pub fn infer_ty_of_term(&self, term: TermId) -> Option<TyId> {
        match self.stores().term().get(term) {
            Term::Runtime(rt_term) => Some(rt_term.term_ty),
            Term::UnionVariant(union_variant) => {
                Some(self.new_ty(Ty::Union(union_variant.original_ty)))
            }
            Term::Tuple(_) => todo!(),
            Term::Lit(_) => todo!(),
            Term::Ctor(_) => {
                todo!()
            }
            Term::FnCall(_) => todo!(),
            Term::FnDef(fn_def_id) => Some(
                self.stores().fn_def().map_fast(fn_def_id, |fn_def| self.new_ty(Ty::Fn(fn_def.ty))),
            ),
            Term::TrtDef(trt_def_id) => {
                Some(self.common_def_ops().compute_fn_ty_of_trt_def(trt_def_id))
            }
            Term::DataDef(data_def_id) => {
                Some(self.common_def_ops().compute_fn_ty_of_data_def(data_def_id))
            }
            Term::ModDef(mod_def_id) => {
                Some(self.common_def_ops().compute_fn_ty_of_mod_def(mod_def_id))
            }
            Term::Block(_) => todo!(),
            Term::Var(_) => todo!(),
            Term::ResolvedVar(_) => todo!(),
            Term::Loop(_) => {
                // @@Future: if loop is proven to not break, return never
                Some(self.new_void_ty())
            }
            Term::LoopControl(_) => todo!(),
            Term::Match(_) => todo!(),
            Term::Return(_) => Some(self.new_never_ty()),
            Term::DeclStackMember(_) => todo!(),
            Term::Assign(_) => todo!(),
            Term::Unsafe(_) => todo!(),
            Term::Access(_) => todo!(),
            Term::Cast(_) => todo!(),
            Term::TypeOf(_) => todo!(),
            Term::Ty(ty_id) => {
                match self.get_ty(ty_id) {
                    Ty::Hole(_) | Ty::Var(_) => None,
                    Ty::Meta(_)
                    | Ty::Union(_)
                    | Ty::Tuple(_)
                    | Ty::Fn(_)
                    | Ty::Ref(_)
                    | Ty::Data(_) => {
                        // @@Todo: bounds
                        Some(self.new_small_universe_ty())
                    }
                    Ty::Universe(universe_ty) => Some(self.new_universe_ty(universe_ty.size + 1)),
                    Ty::ResolvedVar(_) => todo!(),
                    Ty::Eval(_) => todo!(),
                }
            }
            Term::Ref(ref_term) => {
                let inner_ty = self.infer_ty_of_term_or_hole(ref_term.subject);
                Some(self.new_ty(Ty::Ref(RefTy {
                    ty: inner_ty,
                    is_mutable: ref_term.is_mutable,
                    kind: ref_term.kind,
                })))
            }
            Term::Deref(_) => todo!(),
            Term::Hole(_) => None,
        }
    }
}
