use hash_types::new::{
    data::{DataDef, DataDefId},
    environment::env::AccessToEnv,
    fns::{FnDef, FnDefId},
    holes::{Hole, HoleKind},
    params::ParamsId,
    terms::{Term, TermId},
    trts::TrtBoundsId,
    tuples::TupleTy,
    tys::{Ty, TyId, UniverseTy},
    unions::UnionTy,
};
use hash_utils::store::{CloneStore, SequenceStore, Store};

pub trait CommonOps: AccessToEnv {
    fn get_term(&self, term_id: TermId) -> Term {
        self.stores().term().get(term_id)
    }

    fn get_ty(&self, ty_id: TyId) -> Ty {
        self.stores().ty().get(ty_id)
    }

    fn get_data_def(&self, data_def_id: DataDefId) -> DataDef {
        self.stores().data_def().get(data_def_id)
    }

    fn get_fn_def(&self, fn_def_id: FnDefId) -> FnDef {
        self.stores().fn_def().get(fn_def_id)
    }

    fn new_ty(&self, ty: Ty) -> TyId {
        self.stores().ty().create(ty)
    }

    fn new_term(&self, term: Term) -> TermId {
        self.stores().term().create(term)
    }

    fn new_term_hole(&self) -> TermId {
        let hole_id = self.stores().hole().create_with(|id| Hole { id, kind: HoleKind::Term });
        self.stores().term().create_with(|_| Term::Hole(hole_id))
    }

    fn new_ty_hole(&self) -> TyId {
        let hole_id = self.stores().hole().create_with(|id| Hole { id, kind: HoleKind::Ty });
        self.stores().ty().create_with(|_| Ty::Hole(hole_id))
    }

    fn new_empty_params(&self) -> ParamsId {
        self.stores().params().create_from_slice(&[])
    }

    fn new_empty_trt_bounds(&self) -> TrtBoundsId {
        self.stores().trt_bounds().create_from_slice(&[])
    }

    fn new_small_universe_ty(&self) -> TyId {
        self.stores()
            .ty()
            .create(Ty::Universe(UniverseTy { size: 0, trait_bounds: self.new_empty_trt_bounds() }))
    }

    fn new_universe_ty(&self, n: usize) -> TyId {
        self.stores()
            .ty()
            .create(Ty::Universe(UniverseTy { size: n, trait_bounds: self.new_empty_trt_bounds() }))
    }

    fn new_never_ty(&self) -> TyId {
        self.stores().ty().create(Ty::Union(UnionTy { variants: self.new_empty_params() }))
    }

    fn new_void_ty(&self) -> TyId {
        self.stores().ty().create(Ty::Tuple(TupleTy {
            data: self.new_empty_params(),
            conditions: self.new_empty_params(),
        }))
    }
}

impl<T: AccessToEnv> CommonOps for T {}
