use std::{cell::Cell, ops::ControlFlow};

use hash_tir::visitor::Atom;
use hash_utils::derive_more::From;

use crate::errors::TcError;

/// The mode in which to normalise terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NormalisationMode {
    /// Normalise the term as much as possible.
    Full,
    /// Normalise the term to a single step.
    ///
    /// This will not execute any impure code.
    Weak,
}

/// A signal which can be emitted during normalisation.
#[derive(Debug, Clone, From)]
pub enum NormaliseSignal {
    Break,
    Continue,
    Return(Atom),
    Err(TcError),
}

/// The result of a normalisation operation.
pub type NormaliseResult<T> = Result<Option<T>, NormaliseSignal>;

/// Signals that the atom is already normalised.
pub fn already_normalised<T>() -> NormaliseResult<T> {
    Ok(None)
}

/// Signals that the normalisation is stuck.
pub fn stuck_normalising<T>() -> NormaliseResult<T> {
    Ok(None)
}

/// Signals that the normalisation occurred only if the state signifies it.
pub fn normalised_if<T, I: Into<T>>(
    atom: impl FnOnce() -> I,
    state: &NormalisationState,
) -> NormaliseResult<T> {
    if state.has_normalised() {
        Ok(Some(atom().into()))
    } else {
        Ok(None)
    }
}

/// Signals that the normalisation produced the given atom.
pub fn normalised_to<T>(atom: impl Into<T>) -> NormaliseResult<T> {
    Ok(Some(atom.into()))
}

/// Signals that the normalisation produced the given atom, if it is not `None`.
pub fn normalised_option<T>(atom: Option<impl Into<T>>) -> NormaliseResult<T> {
    match atom {
        Some(eval) => normalised_to(eval),
        None => already_normalised(),
    }
}

/// Map the result of a normalisation operation to `ControlFlow::Break(result)`.
///
/// Control-flow normalisation results are used when traversing nested
/// structures, to know whether to continue or break.
pub fn ctrl_map<T>(t: NormaliseResult<T>) -> NormaliseResult<ControlFlow<T>> {
    Ok(t?.map(|t| ControlFlow::Break(t)))
}

/// Create a control-flow normalisation result to continue deeper.
pub fn ctrl_continue<T>() -> NormaliseResult<ControlFlow<T>> {
    Ok(Some(ControlFlow::Continue(())))
}

/// Whether an atom has been evaluated or not.
#[derive(Debug, Clone, Default)]
pub struct NormalisationState {
    has_normalised: Cell<bool>,
}

impl NormalisationState {
    /// Create a new normalisation state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Whether the atom has been normalised.
    pub fn has_normalised(&self) -> bool {
        self.has_normalised.get()
    }

    /// Set the atom as normalised.
    pub fn set_normalised(&self) {
        self.has_normalised.set(true);
    }

    /// Update the state from a normalisation result.
    pub fn update_from_result<T>(
        &self,
        previous: T,
        result: NormaliseResult<T>,
    ) -> Result<T, NormaliseSignal> {
        if let Ok(Some(new)) = result {
            self.set_normalised();
            Ok(new)
        } else if let Err(e) = result {
            Err(e)
        } else {
            Ok(previous)
        }
    }
}
