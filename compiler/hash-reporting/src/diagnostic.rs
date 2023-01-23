//! Reporting diagnostic trait which contains internal logic for
//! adding errors and warnings into an abstract diagnostic store that
//! some stage within the compiler can implement.

use std::{
    cell::RefCell,
    fmt::{self},
    mem::take,
};

use crate::reporter::Reports;

macro_rules! make_diagnostic_traits {
    ($($name:ident with $self_ref:ty),* $(,)?) => {
        $(
        pub trait $name<E, W>: Sized {
            /// Add an error into the [Self]
            fn add_error(self: $self_ref, error: E);

            /// Add an error from a [Result<T, E>] if the result is erroneous.
            fn maybe_add_error<T>(self: $self_ref, value: Result<T, E>) {
                if let Err(e) = value {
                    self.add_error(e);
                }
            }

            /// Add a warning into the diagnostics store.
            fn add_warning(self: $self_ref, warning: W);

            /// Check if the diagnostics has an error.
            fn has_errors(&self) -> bool;

            /// Check if the diagnostics has a warning
            fn has_warnings(&self) -> bool;

            fn has_diagnostics(&self) -> bool {
                self.has_errors() || self.has_warnings()
            }

            /// Convert the [Diagnostics] into a [`Vec<Report>`].
            fn into_reports(
                self: $self_ref,
                make_reports_from_error: impl Fn(E) -> Reports,
                make_reports_from_warning: impl Fn(W) -> Reports,
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
            fn into_diagnostics(self: $self_ref) -> (Vec<E>, Vec<W>);

            /// Merge another diagnostic store with this one.
            fn merge_diagnostics(self: $self_ref, other: impl $name<E, W>);

            /// Clear the diagnostics of all errors and warnings.
            fn clear_diagnostics(self: $self_ref);
        }
        )*
    };
}

make_diagnostic_traits!(Diagnostics with &Self, DiagnosticsMut with &mut Self);

pub struct ImmutableDiagnostics<E, W> {
    pub errors: RefCell<Vec<E>>,
    pub warnings: RefCell<Vec<W>>,
}

impl<E, W> ImmutableDiagnostics<E, W> {
    pub fn new() -> Self {
        Self { errors: RefCell::new(Vec::new()), warnings: RefCell::new(Vec::new()) }
    }
}

impl<E, W> Default for ImmutableDiagnostics<E, W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E: Clone, W: Clone> Clone for ImmutableDiagnostics<E, W> {
    fn clone(&self) -> Self {
        Self {
            errors: RefCell::new(self.errors.borrow().clone()),
            warnings: RefCell::new(self.warnings.borrow().clone()),
        }
    }
}

impl<E: fmt::Debug, W: fmt::Debug> fmt::Debug for ImmutableDiagnostics<E, W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ImmutableDiagnostics")
            .field("errors", &self.errors.borrow())
            .field("warnings", &self.warnings.borrow())
            .finish()
    }
}

impl<E, W> Diagnostics<E, W> for ImmutableDiagnostics<E, W> {
    /// Clear the [DiagnosticStore] of all errors and warnings.
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

    fn into_diagnostics(&self) -> (Vec<E>, Vec<W>) {
        let mut errors = self.errors.borrow_mut();
        let mut warnings = self.warnings.borrow_mut();
        (take(&mut errors), take(&mut warnings))
    }

    fn merge_diagnostics(&self, other: impl Diagnostics<E, W>) {
        let (errors, warnings) = other.into_diagnostics();
        self.errors.borrow_mut().extend(errors);
        self.warnings.borrow_mut().extend(warnings);
    }
}

pub struct MutableDiagnostics<E, W> {
    pub errors: Vec<E>,
    pub warnings: Vec<W>,
}

impl<E, W> MutableDiagnostics<E, W> {
    pub fn new() -> Self {
        Self { errors: Vec::new(), warnings: Vec::new() }
    }
}

impl<E, W> Default for MutableDiagnostics<E, W> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E, W> DiagnosticsMut<E, W> for MutableDiagnostics<E, W> {
    /// Clear the [DiagnosticStore] of all errors and warnings.
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

    fn into_diagnostics(&mut self) -> (Vec<E>, Vec<W>) {
        (take(&mut self.errors), take(&mut self.warnings))
    }

    fn merge_diagnostics(&mut self, mut other: impl DiagnosticsMut<E, W>) {
        let (errors, warnings) = other.into_diagnostics();
        self.errors.extend(errors);
        self.warnings.extend(warnings);
    }
}

/// Convenience trait to allow access to the diagnostics
pub trait AccessToDiagnostics {
    type Error;
    type Warning;
    type Diagnostics: Diagnostics<Self::Error, Self::Warning>;

    fn diagnostics(&self) -> &Self::Diagnostics;

    fn clear_diagnostics(&self) {
        self.diagnostics().clear_diagnostics()
    }

    fn add_error(&self, error: Self::Error) {
        self.diagnostics().add_error(error)
    }

    fn add_warning(&self, warning: Self::Warning) {
        self.diagnostics().add_warning(warning)
    }

    fn has_errors(&self) -> bool {
        self.diagnostics().has_errors()
    }

    fn has_warnings(&self) -> bool {
        self.diagnostics().has_warnings()
    }

    fn merge_diagnostics(&self, other: impl Diagnostics<Self::Error, Self::Warning>) {
        self.diagnostics().merge_diagnostics(other)
    }
}

/// Convenience trait to allow access to the diagnostics
pub trait AccessToDiagnosticsMut {
    type Error;
    type Warning;
    type Diagnostics: DiagnosticsMut<Self::Error, Self::Warning>;

    fn diagnostics(&mut self) -> &mut Self::Diagnostics;

    fn clear_diagnostics(&mut self) {
        self.diagnostics().clear_diagnostics()
    }

    fn add_error(&mut self, error: Self::Error) {
        self.diagnostics().add_error(error)
    }

    fn maybe_add_error<T>(&mut self, value: Result<T, Self::Error>) {
        self.diagnostics().maybe_add_error(value)
    }

    fn add_warning(&mut self, warning: Self::Warning) {
        self.diagnostics().add_warning(warning)
    }

    fn has_errors(&mut self) -> bool {
        self.diagnostics().has_errors()
    }

    fn has_warnings(&mut self) -> bool {
        self.diagnostics().has_warnings()
    }

    fn merge_diagnostics(&mut self, other: impl DiagnosticsMut<Self::Error, Self::Warning>) {
        self.diagnostics().merge_diagnostics(other)
    }
}
