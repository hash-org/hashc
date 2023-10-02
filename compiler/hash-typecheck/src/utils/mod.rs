//! Contains various utilities used by the type checker, which do not fit into
//! any of the `operations` modules.

pub mod cte;
pub mod dumping;
pub mod entry_point;
pub mod exhaustiveness;
pub mod intrinsic_abilities;
pub mod matching;
pub mod normalisation;
pub mod purity;
pub mod substitution;
pub mod unification;
