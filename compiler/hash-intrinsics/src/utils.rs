use hash_tir::new::{
    data::{CtorDefId, CtorPat, CtorTerm, DataTy},
    environment::env::AccessToEnv,
    pats::{Pat, PatId},
    terms::{Term, TermId},
    tys::TyId,
    utils::common::CommonUtils,
};
use hash_utils::store::Store;

use crate::primitives::AccessToPrimitives;

/// Utilities relating to creating and inspecting primitive types.
pub trait PrimitiveUtils: AccessToPrimitives + Sized {
    /// Get the bool constructor for the given value.
    ///
    /// Both constructors do not take arguments.
    fn get_bool_ctor(&self, value: bool) -> CtorDefId {
        let ctor_defs =
            self.stores().data_def().map_fast(self.primitives().bool(), |bool_def| bool_def.ctors);
        match ctor_defs {
            hash_tir::new::data::DataDefCtors::Defined(ctors) => {
                // Index 0 is true, 1 is false, see BootstrapOps
                let idx = if value { 0 } else { 1 };
                (ctors, idx)
            }
            hash_tir::new::data::DataDefCtors::Primitive(_) => {
                panic!("Found primitive data definition for bool")
            }
        }
    }

    /// Create a boolean term of the given value.
    fn new_bool_term(&self, value: bool) -> TermId {
        self.new_term(Term::Ctor(CtorTerm {
            ctor: self.get_bool_ctor(value),
            ctor_args: self.new_empty_def_args(),
            data_args: self.new_empty_def_args(),
        }))
    }

    /// Create a boolean pattern of the given value.
    fn bool_pat(&self, value: bool) -> PatId {
        self.new_pat(Pat::Ctor(CtorPat {
            ctor: self.get_bool_ctor(value),
            ctor_pat_args: self.new_empty_def_pat_args(),
            data_args: self.new_empty_def_args(),
        }))
    }

    /// Create a new `never` type.
    fn new_never_ty(&self) -> TyId {
        self.new_ty(DataTy { args: self.new_empty_def_args(), data_def: self.primitives().never() })
    }
}

impl<T: AccessToEnv + AccessToPrimitives> PrimitiveUtils for T {}
