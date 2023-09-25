use std::cell::Cell;

use hash_tir::tir::{PatId, TermId};
use hash_utils::derive_more::From;

use crate::errors::TcError;

/// A signal which can be emitted during checking.
#[derive(Debug, Clone, From)]
pub enum UnifySignal {
    Stuck,
    CannotUnifyTerms { src: TermId, target: TermId },
    CannotUnifyPats { src: PatId, target: PatId },
    Error(Box<TcError>), // @@Temporary: remove at the end of this transition
}

impl From<TcError> for UnifySignal {
    fn from(err: TcError) -> Self {
        UnifySignal::Error(Box::new(err))
    }
}

impl From<UnifySignal> for TcError {
    fn from(signal: UnifySignal) -> Self {
        match signal {
            UnifySignal::Stuck => TcError::Signal,
            UnifySignal::Error(e) => *e,
            UnifySignal::CannotUnifyTerms { src, target } => {
                TcError::MismatchingTypes { expected: src, actual: target }
            }
            UnifySignal::CannotUnifyPats { src, target } => {
                TcError::MismatchingPats { a: src, b: target }
            }
        }
    }
}

/// The result of a unification operation.
///
/// `Ok(())` means that the unification was successful.
///
/// `Err(Stuck)` means that the unification is stuck.
/// `Err(Error)` means that the unification failed.
pub type UnifyResult<T = ()> = Result<T, UnifySignal>;

/// Signals that the unification is stuck.
pub fn stuck_unifying() -> UnifyResult {
    Err(UnifySignal::Stuck)
}

/// Signals that the unifying is successful.
pub fn unified() -> UnifyResult {
    Ok(())
}

/// Keeps track of the state of a unifying operation.
///
/// This is used to keep track of whether any unifying has happened,
/// and whether any unifying has been stuck.
#[derive(Debug, Clone)]
pub struct UnifyState {
    has_unified: Cell<bool>,
    is_stuck: Cell<bool>,
}

impl Default for UnifyState {
    fn default() -> Self {
        Self::new()
    }
}

impl UnifyState {
    /// Create a new empty unifying state.
    pub fn new() -> Self {
        Self { has_unified: Cell::new(false), is_stuck: Cell::new(false) }
    }

    /// Whether any unifying has successfully happened.
    pub fn has_unified(&self) -> bool {
        self.has_unified.get()
    }

    /// Whether any unifying has been stuck.
    pub fn is_stuck(&self) -> bool {
        self.is_stuck.get()
    }

    /// Signal that this unifying operation is done, and
    /// is either stuck or has unifyed.
    pub fn unified(&self) -> UnifyResult {
        if self.is_stuck() {
            stuck_unifying()
        } else {
            unified()
        }
    }
}
