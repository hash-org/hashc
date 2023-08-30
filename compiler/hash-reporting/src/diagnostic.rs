//! Reporting diagnostic trait which contains internal logic for
//! adding errors and warnings into an abstract diagnostic store that
//! some stage within the compiler can implement.

use std::{
    cell::RefCell,
    fmt::{self},
    mem::take,
};

use hash_utils::thin_vec::ThinVec;

use crate::reporter::Reports;

/// This macro creates `Diagnostics{,Mut}` trait definitions, which provide
/// access to an abstract store containing errors and warnings of some generic
/// type.
macro_rules! make_diagnostic_traits {
    ($($name:ident with $self_ref:ty),* $(,)?) => {
        $(
        pub trait $name: Sized {
            /// The type of error that is stored in the diagnostics.
            type Error;

            /// The type of warning that is stored in the diagnostics.
            type Warning;

            /// Add an error into the [Self]
            fn add_error(self: $self_ref, error: Self::Error);

            /// Add an error from a [Result<T, E>] if the result is erroneous.
            fn maybe_add_error<T>(self: $self_ref, value: Result<T, Self::Error>) {
                if let Err(e) = value {
                    self.add_error(e);
                }
            }

            /// Add a warning into the diagnostics store.
            fn add_warning(self: $self_ref, warning: Self::Warning);

            /// Check if the diagnostics has an error.
            fn has_errors(&self) -> bool;

            /// Check if the diagnostics has a warning
            fn has_warnings(&self) -> bool;

            /// Check if the diagnostics has any errors or warnings.
            fn has_diagnostics(&self) -> bool {
                self.has_errors() || self.has_warnings()
            }

            /// Convert the [Diagnostics] into a [`Vec<Report>`].
            fn into_reports(
                self: $self_ref,
                make_reports_from_error: impl Fn(Self::Error) -> Reports,
                make_reports_from_warning: impl Fn(Self::Warning) -> Reports,
            ) -> Reports {
                let (errors, warnings) = self.into_diagnostics();
                errors
                    .into_iter()
                    .flat_map(make_reports_from_error)
                    .chain(warnings.into_iter().flat_map(make_reports_from_warning))
                    .collect()
            }

            /// Convert the [Diagnostics] into its respective parts.
            ///
            /// This is useful when we just want to get the errors from the diagnostics rather than
            /// immediately converting the diagnostics into [Report]s.
            ///
            /// This will modify self.
            fn into_diagnostics(self: $self_ref) -> (ThinVec<Self::Error>, ThinVec<Self::Warning>);

            /// Merge another diagnostic store with this one.
            fn merge_diagnostics(self: $self_ref, other: impl $name<Error=Self::Error, Warning=Self::Warning>);

            /// Clear the diagnostics of all errors and warnings.
            fn clear_diagnostics(self: $self_ref);
        }
        )*
    };
}

make_diagnostic_traits!(Diagnostics with &Self, DiagnosticsMut with &mut Self);

/// A standard implementation of [Diagnostics] that uses a [RefCell] to store
/// errors and warnings immutably.
pub struct DiagnosticCellStore<E, W> {
    pub errors: RefCell<ThinVec<E>>,
    pub warnings: RefCell<ThinVec<W>>,
}

impl<E, W> DiagnosticCellStore<E, W> {
    pub fn new() -> Self {
        Self { errors: RefCell::new(ThinVec::new()), warnings: RefCell::new(ThinVec::new()) }
    }
}

impl<E, W> Default for DiagnosticCellStore<E, W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E: Clone, W: Clone> Clone for DiagnosticCellStore<E, W> {
    fn clone(&self) -> Self {
        Self {
            errors: RefCell::new(self.errors.borrow().clone()),
            warnings: RefCell::new(self.warnings.borrow().clone()),
        }
    }
}

impl<E: fmt::Debug, W: fmt::Debug> fmt::Debug for DiagnosticCellStore<E, W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ImmutableDiagnostics")
            .field("errors", &self.errors.borrow())
            .field("warnings", &self.warnings.borrow())
            .finish()
    }
}

/// Standard implementation of [Diagnostics] for [ImmutableDiagnostics].
impl<E, W> Diagnostics for DiagnosticCellStore<E, W> {
    type Error = E;
    type Warning = W;

    fn clear_diagnostics(&self) {
        self.errors.borrow_mut().clear();
        self.warnings.borrow_mut().clear();
    }

    fn add_error(&self, error: E) {
        self.errors.borrow_mut().push(error);
    }

    fn add_warning(&self, warning: W) {
        self.warnings.borrow_mut().push(warning);
    }

    fn has_errors(&self) -> bool {
        !self.errors.borrow().is_empty()
    }

    fn has_warnings(&self) -> bool {
        !self.warnings.borrow().is_empty()
    }

    fn into_diagnostics(&self) -> (ThinVec<E>, ThinVec<W>) {
        // This drains all the errors and warnings from the diagnostics store.
        let mut errors = self.errors.borrow_mut();
        let mut warnings = self.warnings.borrow_mut();
        (take(&mut errors), take(&mut warnings))
    }

    fn merge_diagnostics(&self, other: impl Diagnostics<Error = E, Warning = W>) {
        let (errors, warnings) = other.into_diagnostics();
        self.errors.borrow_mut().extend(errors);
        self.warnings.borrow_mut().extend(warnings);
    }
}

/// A standard implementation of [DiagnosticsMut] that stores errors and
/// warnings directly, and thus is mutable.
pub struct DiagnosticStore<E, W> {
    pub errors: ThinVec<E>,
    pub warnings: ThinVec<W>,
}

impl<E, W> DiagnosticStore<E, W> {
    pub fn new() -> Self {
        Self { errors: ThinVec::new(), warnings: ThinVec::new() }
    }
}

impl<E, W> Default for DiagnosticStore<E, W> {
    fn default() -> Self {
        Self::new()
    }
}

/// Standard implementation of [DiagnosticsMut] for [MutableDiagnostics].
impl<E, W> DiagnosticsMut for DiagnosticStore<E, W> {
    type Error = E;
    type Warning = W;

    fn clear_diagnostics(&mut self) {
        self.errors.clear();
        self.warnings.clear();
    }

    fn add_error(&mut self, error: E) {
        self.errors.push(error);
    }

    fn add_warning(&mut self, warning: W) {
        self.warnings.push(warning);
    }

    fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }

    fn into_diagnostics(&mut self) -> (ThinVec<E>, ThinVec<W>) {
        (take(&mut self.errors), take(&mut self.warnings))
    }

    fn merge_diagnostics(&mut self, mut other: impl DiagnosticsMut<Error = E, Warning = W>) {
        let (errors, warnings) = other.into_diagnostics();
        self.errors.extend(errors);
        self.warnings.extend(warnings);
    }
}

/// Convenience trait to allow access to the diagnostics
///
/// API follows the [Diagnostics] trait.
pub trait AccessToDiagnostics {
    type Diagnostics: Diagnostics;

    fn diagnostics(&self) -> &Self::Diagnostics;

    fn clear_diagnostics(&self) {
        self.diagnostics().clear_diagnostics()
    }

    fn add_error(&self, error: <Self::Diagnostics as Diagnostics>::Error) {
        self.diagnostics().add_error(error)
    }

    fn maybe_add_error<T>(&mut self, value: Result<T, <Self::Diagnostics as Diagnostics>::Error>) {
        self.diagnostics().maybe_add_error(value)
    }

    fn add_warning(&self, warning: <Self::Diagnostics as Diagnostics>::Warning) {
        self.diagnostics().add_warning(warning)
    }

    fn has_errors(&self) -> bool {
        self.diagnostics().has_errors()
    }

    fn has_warnings(&self) -> bool {
        self.diagnostics().has_warnings()
    }

    fn merge_diagnostics(
        &self,
        other: impl Diagnostics<
            Error = <Self::Diagnostics as Diagnostics>::Error,
            Warning = <Self::Diagnostics as Diagnostics>::Warning,
        >,
    ) {
        self.diagnostics().merge_diagnostics(other)
    }
}

/// Convenience trait to allow access to the diagnostics
///
/// API follows the [DiagnosticsMut] trait.
pub trait AccessToDiagnosticsMut {
    type Diagnostics: DiagnosticsMut;

    fn diagnostics(&mut self) -> &mut Self::Diagnostics;

    fn clear_diagnostics(&mut self) {
        self.diagnostics().clear_diagnostics()
    }

    fn add_error(&mut self, error: <Self::Diagnostics as DiagnosticsMut>::Error) {
        self.diagnostics().add_error(error)
    }

    fn maybe_add_error<T>(
        &mut self,
        value: Result<T, <Self::Diagnostics as DiagnosticsMut>::Error>,
    ) {
        self.diagnostics().maybe_add_error(value)
    }

    fn add_warning(&mut self, warning: <Self::Diagnostics as DiagnosticsMut>::Warning) {
        self.diagnostics().add_warning(warning)
    }

    fn has_errors(&mut self) -> bool {
        self.diagnostics().has_errors()
    }

    fn has_warnings(&mut self) -> bool {
        self.diagnostics().has_warnings()
    }

    fn merge_diagnostics(
        &mut self,
        other: impl DiagnosticsMut<
            Error = <Self::Diagnostics as DiagnosticsMut>::Error,
            Warning = <Self::Diagnostics as DiagnosticsMut>::Warning,
        >,
    ) {
        self.diagnostics().merge_diagnostics(other)
    }
}

/// A convenient trait which specifies that an error type can be converted
/// into a compound error version.
pub trait IntoCompound: Sized {
    fn into_compound(items: Vec<Self>) -> Self;
}

/// Accumulates errors that occur during typechecking in a local scope.
///
/// This is used for error recovery, so that multiple errors can be reported
/// at once.
#[derive(Debug)]
pub struct ErrorState<E> {
    pub errors: Vec<E>,
}

impl<E> ErrorState<E> {
    /// Create a new [ErrorState].
    pub fn new() -> Self {
        Self { errors: vec![] }
    }

    /// Add an error to the error state.
    pub fn add_error(&mut self, error: impl Into<E>) -> &E {
        let error = error.into();
        self.errors.push(error);
        self.errors.last().unwrap()
    }

    /// Add an error to the error state if the given result is an error.
    pub fn try_or_add_error<F>(&mut self, f: Result<F, E>) -> Option<F> {
        match f {
            Ok(v) => Some(v),
            Err(e) => {
                self.add_error(e);
                None
            }
        }
    }

    /// Add a set of errors to the error state.
    pub fn add_errors(&mut self, errors: impl IntoIterator<Item = impl Into<E>>) {
        self.errors.extend(errors.into_iter().map(|err| err.into()));
    }

    /// Whether the error state has any errors.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Take the errors from the error state.
    pub fn take_errors(&mut self) -> Vec<E> {
        std::mem::take(&mut self.errors)
    }
}

impl<E: IntoCompound> ErrorState<E> {
    /// Convert the accumulated [ErrorState] into a single error. This is
    /// possible since [ErrorState] implements [IntoCompound].
    pub fn into_error<T>(&mut self, t: impl FnOnce() -> Result<T, E>) -> Result<T, E> {
        if self.has_errors() {
            let errors = self.take_errors();
            Err(E::into_compound(errors))
        } else {
            t()
        }
    }
}

impl<E> Default for ErrorState<E> {
    fn default() -> Self {
        Self::new()
    }
}
