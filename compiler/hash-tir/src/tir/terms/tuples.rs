//! Definitions related to tuples.

use std::fmt::Display;

use crate::tir::{ArgsId, ParamsId, PatArgsId, PatArgsWithSpread, Spread};

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
/// This is, in its most general form, `(a_1 = s_1,...,a_n = s_n)`.
#[derive(Debug, Clone, Copy)]
pub struct TupleTerm {
    /// The arguments given for the tuple, `(s_1,...,s_n)`
    pub data: ArgsId,
}

impl Display for TupleTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        write!(f, "{}", self.data)?;
        write!(f, ")")
    }
}

impl Display for TupleTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        write!(f, "{}", self.data)?;
        write!(f, ")")
    }
}
