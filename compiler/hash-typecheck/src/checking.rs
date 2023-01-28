//! Contains utilities to perform type checking.

use derive_more::{Constructor, Deref};

use crate::AccessToTypechecking;

#[derive(Constructor, Deref)]
pub struct CheckingOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> CheckingOps<'_, T> {}
