use derive_more::Constructor;

use super::common::CommonUtils;
use crate::{
    impl_access_to_env,
    new::{
        environment::env::Env,
        tuples::TupleTerm,
        tys::{Ty, TyId},
    },
};

#[derive(Constructor)]
pub struct TupleUtils<'tc> {
    env: &'tc Env<'tc>,
}

impl_access_to_env!(TupleUtils<'tc>);

impl<'tc> TupleUtils<'tc> {
    pub fn infer_ty_of_tuple(&self, tuple: &TupleTerm) -> TyId {
        if let Some(original_ty) = tuple.original_ty {
            return self.new_ty(Ty::Tuple(original_ty));
        }
        todo!()
    }
}
