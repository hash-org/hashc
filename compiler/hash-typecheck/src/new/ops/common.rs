use hash_types::new::{
    data::{DataDef, DataDefId},
    environment::env::AccessToEnv,
    holes::{Hole, HoleKind},
    terms::{Term, TermId},
    tys::{Ty, TyId, UniverseTy},
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

    fn new_small_universe_ty(&self) -> TyId {
        self.stores().ty().create(Ty::Universe(UniverseTy {
            size: 0,
            trait_bounds: self.stores().trt_bounds().create_from_slice(&[]),
        }))
    }

    fn new_universe_ty(&self, n: usize) -> TyId {
        self.stores().ty().create(Ty::Universe(UniverseTy {
            size: n,
            trait_bounds: self.stores().trt_bounds().create_from_slice(&[]),
        }))
    }
}

impl<T: AccessToEnv> CommonOps for T {}
