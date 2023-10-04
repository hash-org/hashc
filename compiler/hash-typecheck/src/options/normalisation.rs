//! Various structures that are used to keep track of normalisation progress and
//! options that can be set for normalisation.
use std::{cell::Cell, ops::ControlFlow};

use hash_tir::tir::TermId;
use hash_utils::{derive_more::From, state::LightState};

use crate::diagnostics::TcError;

/// A signal which can be emitted during normalisation.
#[derive(Debug, Clone, From)]
pub enum NormaliseSignal {
    /// A [`LoopControlTerm::Break`](hash_tir::tir::LoopControlTerm::Break) was
    /// encountered in a loop.
    Break,
    /// A [`LoopControlTerm::Continue`](`hash_tir::tir::LoopControlTerm::Continue`) was encountered in a
    /// loop.
    Continue,
    /// A `ReturnTerm` was encountered in a function, with the given return
    /// value.
    Return(TermId),
    /// An typechecking error occurred during normalisation.
    Err(TcError),
}

/// The result of a normalisation operation.
///
/// - `Err(e)` means that the normalisation has stopped with the given signal.
///   This might be an error, or some other signal such as a loop break or a
///   function return.
///
/// - `Ok(None)` means that the normalisation was completed but the atom was
///   already normalised so nothing needed to be done.
///
/// - `Ok(Some(t))` means that the normalisation was completed and the atom was
///   normalised to `t`
///
/// Usually this type is used with `T = ControlFlow<U>` for some `U`. In this
/// case, `ControlFlow::Break` is used to signal that the normalisation was
/// completed and the atom was normalised to some `u: U`, and
/// `ControlFlow::Continue` is used to signal that the normalisation should
/// continue by recursing into the input `U`.
// @@Improvement: maybe we can make this into a custom enum and implement
// `std::ops::Try` for it?
pub type NormaliseResult<T = ()> = Result<Option<T>, NormaliseSignal>;

/// Signals that the atom is already normalised.
pub fn already_normalised<T>() -> NormaliseResult<T> {
    Ok(None)
}

/// Signals that the normalisation is stuck.
///
/// This is equivalent to the atom being already normalised, since no more
/// steps can be taken. The difference is mostly for visual clarity.
pub fn stuck_normalising<T>() -> NormaliseResult<T> {
    Ok(None)
}

/// Signals that the normalisation occurred only if the state signifies it.
pub fn normalised_if<T, I: Into<T>>(
    atom: impl FnOnce() -> I,
    state: &NormalisationState,
) -> NormaliseResult<ControlFlow<T>> {
    if state.has_normalised() {
        Ok(Some(ControlFlow::Break(atom().into())))
    } else {
        Ok(None)
    }
}

/// Signals that the normalisation was successful.
pub fn normalised() -> NormaliseResult<()> {
    Ok(Some(()))
}

/// Signals that the atom should be normalised by recursing into its children.
pub fn normalise_nested<T>() -> NormaliseResult<ControlFlow<T>> {
    Ok(Some(ControlFlow::Continue(())))
}

/// Signals that the normalisation produced the given atom.
pub fn normalised_to<T>(atom: impl Into<T>) -> NormaliseResult<ControlFlow<T>> {
    Ok(Some(ControlFlow::Break(atom.into())))
}

/// Signals that the normalisation produced the given atom, if it is not `None`.
pub fn normalised_option<T>(atom: Option<impl Into<T>>) -> NormaliseResult<ControlFlow<T>> {
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

/// Lift a `From` implementation into a conversion between normalisation
/// results containing `ControlFlow`.
pub fn normalisation_result_control_flow_into<T, U: From<T>>(
    t: NormaliseResult<ControlFlow<T>>,
) -> NormaliseResult<ControlFlow<U>> {
    match t {
        Ok(Some(ControlFlow::Break(t))) => Ok(Some(ControlFlow::Break(t.into()))),
        Ok(Some(ControlFlow::Continue(()))) => Ok(Some(ControlFlow::Continue(()))),
        Ok(None) => Ok(None),
        Err(e) => Err(e),
    }
}

/// Lift a `From` implementation into a conversion between normalisation
/// results.
pub fn normalisation_result_into<T, U: From<T>>(t: NormaliseResult<T>) -> NormaliseResult<U> {
    match t {
        Ok(Some(t)) => Ok(Some(t.into())),
        Ok(None) => Ok(None),
        Err(e) => Err(e),
    }
}

/// Used to keep track of whether normalisation has occurred or not.
///
/// Multiple normalisation operations can update the state, and in the end
/// the accumulated result can be read through `has_normalised()`.
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

    /// Signal that the normalisation is done, and produce
    /// an appropriate result.
    pub fn done(&self) -> NormaliseResult {
        if self.has_normalised() {
            Ok(Some(()))
        } else {
            Ok(None)
        }
    }
}

/// The mode in which to normalise terms.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum NormalisationMode {
    /// Normalise the term as much as possible.
    Full,
    /// Normalise the term to a single step.
    ///
    /// This will not execute any impure code.
    #[default]
    Weak,
}

/// Options that can be applied to a normalisation operation.
#[derive(Clone, Debug)]
pub struct NormalisationOptions {
    /// The mode in which to normalise terms.
    pub mode: LightState<NormalisationMode>,
}

impl Default for NormalisationOptions {
    fn default() -> Self {
        Self::new()
    }
}

impl NormalisationOptions {
    pub fn new() -> Self {
        Self { mode: LightState::new(NormalisationMode::default()) }
    }
}
