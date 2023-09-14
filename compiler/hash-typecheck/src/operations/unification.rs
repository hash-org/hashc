use std::cell::Cell;

use hash_utils::derive_more::From;

use super::checking::CheckSignal;
use crate::errors::{TcError, TcResult};

/// A signal which can be emitted during checking.
#[derive(Debug, Clone, From)]
pub enum UnifySignal {
    Stuck,
    Error(Box<TcError>),
}

impl From<TcError> for UnifySignal {
    fn from(error: TcError) -> Self {
        Self::Error(Box::new(error))
    }
}

impl From<CheckSignal> for UnifySignal {
    fn from(signal: CheckSignal) -> Self {
        match signal {
            CheckSignal::Stuck => Self::Stuck,
            CheckSignal::Error(e) => Self::Error(e),
        }
    }
}

/// The result of a unification operation.
///
/// `Ok(())` means that the unification was successful.
///
/// `Err(Stuck)` means that the unification is stuck.
/// `Err(Error)` means that the unification failed.
pub type UnifyResult = Result<(), UnifySignal>;

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

    /// Add the result of a unifying operation to the state.
    pub fn then(&self, result: UnifyResult) -> TcResult<()> {
        match result {
            Ok(()) => Ok(()),
            Err(e) => match e {
                UnifySignal::Stuck => {
                    self.is_stuck.set(true);
                    Ok(())
                }
                UnifySignal::Error(e) => Err(*e),
            },
        }
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
