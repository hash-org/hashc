use derive_more::Constructor;
use hash_types::{
    impl_access_to_env,
    new::{
        data::{CtorDefId, CtorPat, CtorTerm},
        environment::env::{AccessToEnv, Env},
        pats::{Pat, PatId},
        terms::{Term, TermId},
        utils::common::CommonUtils,
    },
};
use hash_utils::store::Store;

use crate::primitives::DefinedPrimitives;

#[derive(Constructor)]
pub struct IntrinsicUtils<'env> {
    env: &'env Env<'env>,
    primitives: &'env DefinedPrimitives,
}

impl_access_to_env!(IntrinsicUtils<'env>);

impl<'env> IntrinsicUtils<'env> {
    pub fn primitives(&self) -> &DefinedPrimitives {
        self.primitives
    }

    /// Get the bool constructor for the given value.
    ///
    /// Both constructors do not take arguments.
    pub fn get_bool_ctor(&self, value: bool) -> CtorDefId {
        let ctor_defs =
            self.stores().data_def().map_fast(self.primitives().bool(), |bool_def| bool_def.ctors);
        match ctor_defs {
            hash_types::new::data::DataDefCtors::Defined(ctors) => {
                // Index 0 is true, 1 is false, see BootstrapOps
                let idx = if value { 0 } else { 1 };
                (ctors, idx)
            }
            hash_types::new::data::DataDefCtors::Primitive(_) => {
                panic!("Found primitive data definition for bool")
            }
        }
    }

    /// Create a boolean term of the given value.
    pub fn new_bool_term(&self, value: bool) -> TermId {
        self.new_term(Term::Ctor(CtorTerm {
            ctor: self.get_bool_ctor(value),
            ctor_args: self.new_empty_def_args(),
            data_args: self.new_empty_def_args(),
        }))
    }

    /// Create a boolean pattern of the given value.
    pub fn bool_pat(&self, value: bool) -> PatId {
        self.new_pat(Pat::Ctor(CtorPat {
            ctor: self.get_bool_ctor(value),
            ctor_pat_args: self.new_empty_def_pat_args(),
            data_args: self.new_empty_def_args(),
        }))
    }
}
