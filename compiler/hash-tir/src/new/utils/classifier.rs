//! Classification of primitives
use derive_more::Constructor;

use crate::{impl_access_to_env, new::environment::env::Env};

/// Classification of primitives
#[derive(Constructor)]
pub struct Classifier<'env> {
    env: &'env Env<'env>,
}

impl_access_to_env!(Classifier<'tc>);

pub enum LitTy {
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    U128,
    I128,
    IBig,
    UBig,
    F32,
    F64,
    Bool,
}

impl<'env> Classifier<'env> {}
