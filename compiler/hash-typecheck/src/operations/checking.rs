use std::cell::Cell;

use hash_tir::tir::{NodeOrigin, ParamError, Ty, TyId};
use hash_utils::derive_more::From;

use super::unification::UnifySignal;
use crate::{
    checker::Checker,
    env::TcEnv,
    errors::{TcError, TcResult},
};

/// A signal which can be emitted during checking.
#[derive(Debug, Clone, From)]
pub enum CheckSignal {
    Stuck,
    Error(Box<TcError>),
}

impl From<UnifySignal> for CheckSignal {
    fn from(signal: UnifySignal) -> Self {
        match signal {
            UnifySignal::Stuck => Self::Stuck,
            UnifySignal::Error(e) => Self::Error(e),
        }
    }
}

impl From<TcError> for CheckSignal {
    fn from(error: TcError) -> Self {
        Self::Error(Box::new(error))
    }
}

impl From<ParamError> for CheckSignal {
    fn from(error: ParamError) -> Self {
        Self::Error(Box::new(TcError::from(error)))
    }
}

/// The result of a checking operation.
///
/// `Ok(true)` means that the checking was successful.
/// `Ok(false)` means that the checking was unnecessary.
///
/// `Err(Stuck)` means that the checking is stuck.
/// `Err(Error)` means that the checking failed.
pub type CheckResult<T = ()> = Result<Check<T>, CheckSignal>;

pub struct Check<T> {
    pub progress: bool,
    pub result: T,
}

/// Signals that the checking is stuck.
pub fn stuck_checking<T>() -> CheckResult<T> {
    Err(CheckSignal::Stuck)
}

/// Signals that the checking is successful.
pub fn did_check<T>(t: T) -> CheckResult<T> {
    Ok(Check { progress: true, result: t })
}

/// Signals that the checking is unnecessary/has already happened.
pub fn already_checked<T>(t: T) -> CheckResult<T> {
    Ok(Check { progress: false, result: t })
}

/// Keeps track of the state of a checking operation.
///
/// This is used to keep track of whether any checking has happened,
/// and whether any checking has been stuck.
#[derive(Debug, Clone)]
pub struct CheckState {
    progress: Cell<bool>,
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
        Self { progress: Cell::new(false), is_stuck: Cell::new(false) }
    }

    /// Whether any checking has successfully happened.
    pub fn has_checked(&self) -> bool {
        self.progress.get()
    }

    /// Whether any checking has been stuck.
    pub fn is_stuck(&self) -> bool {
        self.is_stuck.get()
    }

    /// Add the result of a checking operation to the state, and
    /// return its data if applicable.
    ///
    /// If the checking operation is stuck, then return an appropriate
    /// error.
    ///
    /// @@Temporary: until the old inference code is removed.
    #[inline]
    pub fn then_result<T>(&self, result: CheckResult<T>) -> TcResult<T> {
        match result {
            Ok(check) => {
                let current = self.progress.get();
                self.progress.set(current || check.progress);
                Ok(check.result)
            }
            Err(e) => match e {
                CheckSignal::Stuck => {
                    self.is_stuck.set(true);
                    Err(TcError::Signal)
                }
                CheckSignal::Error(e) => Err(*e),
            },
        }
    }

    /// Add the result of a checking operation to the state.
    #[inline]
    pub fn then(&self, result: CheckResult) -> TcResult<()> {
        match result {
            Ok(check) => {
                let current = self.progress.get();
                self.progress.set(current || check.progress);
                Ok(())
            }
            Err(e) => match e {
                CheckSignal::Stuck => {
                    self.is_stuck.set(true);
                    Ok(())
                }
                CheckSignal::Error(e) => Err(*e),
            },
        }
    }

    /// Signal that this checking operation is done, and
    /// is either stuck or has definitely checked.
    #[inline]
    pub fn done_and_checked(&self) -> CheckResult {
        if self.is_stuck() {
            stuck_checking()
        } else {
            did_check(())
        }
    }

    /// Signal that this checking operation is done, and
    /// is either stuck or has checked if some child has checked.
    #[inline]
    pub fn done(&self) -> CheckResult {
        if self.is_stuck() {
            stuck_checking()
        } else if self.has_checked() {
            did_check(())
        } else {
            already_checked(())
        }
    }
}

impl<E: TcEnv> Checker<'_, E> {
    pub fn check_is_universe(&self, ty: TyId) -> CheckResult {
        self.uni_ops().unify_terms(ty, Ty::universe(NodeOrigin::Expected))?;
        CheckState::new().done()
    }
}
