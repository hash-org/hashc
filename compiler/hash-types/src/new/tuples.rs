//! Definitions related to tuples.

use crate::new::{args::ArgsId, params::ParamsId};

/// A tuple type.
///
/// This is, in its most general form, `(a_1:A_1,...,a_n:A_n) where
/// (p_1:P_1,...p_m:P_m)`.
#[derive(Debug, Clone, Copy)]
pub struct TupleTy {
    /// The parameters of the tuple, `(a_1:A_1,...,a_n:A_n)`.
    pub data: ParamsId,
    /// The conditions of the tuple, `where (p_1:P_1,...,p_m:P_m)`.
    pub conditions: ParamsId,
}

/// A tuple term.
///
/// This is, in its most general form, `(a_1:A_1 = s_1,...,a_n:A_n = s_n) where
/// (p_1:P_1 = q_1,...p_m:P_m = q_m)`.
#[derive(Debug, Clone, Copy)]
pub struct TupleTerm {
    /// The original tuple type, if known or given as part of the literal (might
    /// contain holes).
    pub original_ty: Option<TupleTy>,

    /// The arguments given for the tuple, `(s_1,...,s_n)`
    ///
    /// If the original type is present, then this is sorted in the order of the
    /// parameters.
    pub data: ArgsId,

    /// Condition arguments, if given, `where (p_1,...,p_m)`.
    ///
    /// This should be present if `original_ty` is present (even if it is an
    /// empty tuple).
    /// It could also be present if `original_ty` is not present, but then they
    /// will eventually be unified with the original type when the latter is
    /// resolved.
    pub conditions: ArgsId,
}
