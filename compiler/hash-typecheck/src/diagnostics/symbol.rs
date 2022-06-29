//! Error-related data structures for errors that in regards to symbols
//! and symbols within error variants.

use std::fmt::Display;

use crate::storage::{
    primitives::{Level0Term, Level1Term, Term},
    terms::TermStore,
};

/// An enum representing the origin of a named field access.
/// This is used to provide additional contextual information
/// when the validator fails to find a named field within
/// an enumeration or similar kind of [Term]. The error that
/// the validator generates with this value in mind is
/// [super::error::TcError::UnresolvedNameInValue].
#[derive(Debug, Clone)]
pub enum NameFieldOrigin {
    /// Enum nominal definition
    Enum,
    /// Inner variant of an enum
    EnumVariant,
    /// Impl or module block, unclear which it is but it shouldn't matter.
    Mod,
    /// Tuple parent subject
    Tuple,
}

impl NameFieldOrigin {
    /// Utility function to convert a [Term] into a [NameFieldOrigin].
    ///
    /// This assumes that the provided term does yield a [NameFieldOrigin]
    /// and any other variant of term will cause the function to *panic*.
    pub fn new_from_term(term: &Term, store: &TermStore) -> Self {
        let term_from_level_1 = |t: &Level1Term| match t {
            Level1Term::ModDef(_) => Self::Mod,
            Level1Term::NominalDef(_) => Self::Enum,
            Level1Term::Tuple(_) => Self::Tuple,
            Level1Term::Fn(_) => unreachable!(),
        };

        match term {
            Term::Level1(inner) => term_from_level_1(inner),
            Term::Level0(Level0Term::Rt(inner)) => {
                // we can extract the inner type since it's
                // known that this should be a level-1 term
                NameFieldOrigin::new_from_term(store.get(*inner), store)
            }
            _ => unreachable!(),
        }
    }
}

impl Display for NameFieldOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NameFieldOrigin::Enum => write!(f, "enum"),
            NameFieldOrigin::EnumVariant => write!(f, "enum variant"),
            NameFieldOrigin::Mod => write!(f, "impl block"),
            NameFieldOrigin::Tuple => write!(f, "tuple"),
        }
    }
}
