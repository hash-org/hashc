use std::cell::Cell;

use hash_utils::derive_more::From;

use crate::errors::TcError;

/// A signal which can be emitted during checking.
#[derive(Debug, Clone, From)]
pub enum CheckSignal {
    Stuck,
    Error(TcError),
}

/// The result of a checking operation.
///
/// `Ok(true)` means that the checking was successful.
/// `Ok(false)` means that the checking was unnecessary.
///
/// `Err(Stuck)` means that the checking is stuck.
/// `Err(Error)` means that the checking failed.
pub type CheckResult = Result<bool, CheckSignal>;

/// Signals that the checking is stuck.
pub fn stuck_checking() -> CheckResult {
    Err(CheckSignal::Stuck)
}

/// Signals that the checking is successful.
pub fn checked() -> CheckResult {
    Ok(true)
}

/// Signals that the checking is unnecessary/has already happened.
pub fn already_checked() -> CheckResult {
    Ok(false)
}

/// Keeps track of the state of a checking operation.
///
/// This is used to keep track of whether any checking has happened,
/// and whether any checking has been stuck.
#[derive(Debug, Clone)]
pub struct CheckState {
    has_checked: Cell<bool>,
    is_stuck: Cell<bool>,
}

impl Default for CheckState {
    fn default() -> Self {
        Self::new()
    }
}

impl CheckState {
    /// Create a new empty checking state.
    pub fn new() -> Self {
        Self { has_checked: Cell::new(false), is_stuck: Cell::new(false) }
    }

    /// Whether any checking has successfully happened.
    pub fn has_checked(&self) -> bool {
        self.has_checked.get()
    }

    /// Whether any checking has been stuck.
    pub fn is_stuck(&self) -> bool {
        self.is_stuck.get()
    }

    /// Add the result of a checking operation to the state.
    pub fn then(&self, result: CheckResult) -> Result<(), TcError> {
        match result {
            Ok(has_checked) => {
                let current = self.has_checked.get();
                self.has_checked.set(current || has_checked);
                Ok(())
            }
            Err(e) => match e {
                CheckSignal::Stuck => {
                    self.is_stuck.set(true);
                    Ok(())
                }
                CheckSignal::Error(e) => Err(e),
            },
        }
    }

    /// Signal that this checking operation is done, and
    /// is either stuck or has definitely checked.
    pub fn done_and_checked(&self) -> CheckResult {
        if self.is_stuck() {
            stuck_checking()
        } else {
            checked()
        }
    }

    /// Signal that this checking operation is done, and
    /// is either stuck or has checked if some child has checked.
    pub fn done(&self) -> CheckResult {
        if self.is_stuck() {
            stuck_checking()
        } else if self.has_checked() {
            checked()
        } else {
            already_checked()
        }
    }
}
