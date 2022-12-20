use derive_more::Constructor;
use hash_types::new::{
    tuples::TupleTerm,
    tys::{Ty, TyId},
};

use super::common::CommonOps;
use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

#[derive(Constructor)]
pub struct TupleOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(TupleOps<'tc>);

impl<'tc> TupleOps<'tc> {
    pub fn infer_ty_of_tuple(&self, tuple: &TupleTerm) -> TyId {
        if let Some(original_ty) = tuple.original_ty {
            return self.new_ty(Ty::Tuple(original_ty));
        }
        todo!()
    }
}
