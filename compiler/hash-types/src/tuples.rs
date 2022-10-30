use crate::{arguments::ArgsIdOld, params::ParamsId};

/// A tuple type.
#[derive(Debug, Clone, Copy)]
pub struct TupleTy {
    pub data: ParamsId,
    pub conditions: ParamsId,
}

/// A tuple term.
#[derive(Debug, Clone, Copy)]
pub struct TupleTerm {
    /// The original tuple type, if known.
    pub original_ty: Option<TupleTy>,

    /// If params is present, then this is sorted in the order of the
    /// parameters.
    pub data: ArgsIdOld,

    /// Condition arguments, if given.
    pub conditions: ArgsIdOld,
}
