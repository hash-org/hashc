//! Reporting diagnostic trait which contains internal logic for
//! adding errors and warnings into an abstract diagnostic store that
//! some stage within the compiler can implement.

use crate::report::Report;

pub trait Diagnostics<E, W> {
    /// The store that is used to store the relevant diagnostics,
    /// this is up to the implementation of the trait how the
    /// store is implemented.
    type DiagnosticsStore;

    /// Get a reference to the associated [Self::DiagnosticsStore]
    fn diagnostic_store(&self) -> &Self::DiagnosticsStore;

    /// Add an error into the [Self]
    fn add_error(&mut self, error: E);

    /// Add an error from a [Result<T, E>] if the result is erroneous.
    fn maybe_add_error<T>(&mut self, value: Result<T, E>) {
        if let Err(e) = value {
            self.add_error(e);
        }
    }

    /// Add a warning into the diagnostics store.
    fn add_warning(&mut self, warning: W);

    /// Check if the diagnostics has an error.
    fn has_errors(&self) -> bool;

    /// Check if the diagnostics has a warning
    fn has_warnings(&self) -> bool;

    fn has_diagnostics(&self) -> bool {
        self.has_errors() || self.has_warnings()
    }

    /// Convert the [Diagnostics] into a [Vec<Report>].
    fn into_reports(self) -> Vec<Report>;

    /// Convert the [Diagnostics] into it's respective parts.
    /// This is useful
    /// when we just want to get the errors from the diagnostics
    /// rather than immediately converting the diagnostics into
    /// [Report]s.
    fn into_diagnostics(self) -> (Vec<E>, Vec<W>);

    /// Merge another diagnostic store with this one.
    fn merge_diagnostics(&mut self, other: impl Diagnostics<E, W>);
}
