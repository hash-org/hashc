//! Definitions related to tuples.

use std::fmt::Display;

use crate::tir::{ArgsId, ModDefId, ParamsId, PatArgsId, PatArgsWithSpread, Spread};

/// The kind of the tuple.
#[derive(Debug, Clone, Copy)]
pub enum TupleKind {
    /// A defined module.
    Mod(ModDefId),
    /// An anonymous tuple `(...)` literal.
    Anon,
}

/// A tuple type.
///
/// This is, in its most general form, `(a_1:A_1,...,a_n:A_n)`.
#[derive(Debug, Clone, Copy)]
pub struct TupleTy {
    /// The parameters of the tuple, `(a_1:A_1,...,a_n:A_n)`.
    pub data: ParamsId,
}

/// A tuple term, which either represents a tuple literal or a module.
///
/// This is, in its most general form, `(a_1 = s_1,...,a_n = s_n)`.
#[derive(Debug, Clone, Copy)]
pub struct TupleTerm {
    /// The kind of the tuple.
    pub kind: TupleKind,
    /// The arguments given for the tuple, `(s_1,...,s_n)`
    pub data: ArgsId,
}

/// A tuple pattern
///
/// This is, in its most general form, `(a_1 = s_1,...,a_n = s_n)`.
#[derive(Debug, Clone, Copy)]
pub struct TuplePat {
    /// The pattern arguments given for the tuple, `(s_1,...,s_n)`
    pub data: PatArgsId,

    /// The spread in the data patterns, if any.
    pub data_spread: Option<Spread>,
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

impl Display for TuplePat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        write!(f, "{}", PatArgsWithSpread::from((self.data, self.data_spread)))?;
        write!(f, ")")
    }
}
