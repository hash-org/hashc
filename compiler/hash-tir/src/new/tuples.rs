//! Definitions related to tuples.

use std::fmt::Display;

use super::{
    args::PatArgsId,
    environment::env::{AccessToEnv, WithEnv},
    pats::Spread,
};
use crate::new::{args::ArgsId, params::ParamsId};

/// A tuple type.
///
/// This is, in its most general form, `(a_1:A_1,...,a_n:A_n)`.
#[derive(Debug, Clone, Copy)]
pub struct TupleTy {
    /// The parameters of the tuple, `(a_1:A_1,...,a_n:A_n)`.
    pub data: ParamsId,
}

/// A tuple term.
///
/// This is, in its most general form, `(a_1:A_1 = s_1,...,a_n:A_n = s_n)`.
#[derive(Debug, Clone, Copy)]
pub struct TupleTerm {
    /// The original tuple type, if known or given as part of the literal (might
    /// contain holes).
    // pub original_ty: Option<TupleTy>,

    /// The arguments given for the tuple, `(s_1,...,s_n)`
    ///
    /// If the original type is present, then this is sorted in the order of the
    /// parameters.
    pub data: ArgsId,
}

/// A tuple pattern
///
/// This is, in its most general form, `(a_1:A_1 = s_1,...,a_n:A_n = s_n)`.
#[derive(Debug, Clone, Copy)]
pub struct TuplePat {
    /// The original tuple type, if known or given as part of the literal (might
    /// contain holes).
    // pub original_ty: Option<TupleTy>,

    /// The pattern arguments given for the tuple, `(s_1,...,s_n)`
    ///
    /// If the original type is present, then this is sorted in the order of the
    /// parameters.
    pub data: PatArgsId,

    /// The spread in the data patterns, if any.
    pub data_spread: Option<Spread>,
}

impl Display for WithEnv<'_, &TupleTy> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        write!(f, "{}", self.env().with(self.value.data))?;
        write!(f, ")")
    }
}

impl Display for WithEnv<'_, &TupleTerm> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        write!(f, "{}", self.env().with(self.value.data))?;
        write!(f, ")")
    }
}

impl Display for WithEnv<'_, &TuplePat> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        write!(f, "{}", self.env().with(self.value.data))?;
        write!(f, ")")
    }
}
