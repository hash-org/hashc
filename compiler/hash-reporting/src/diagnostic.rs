//! Reporting diagnostic trait which contains internal logic for
//! adding errors and warnings into an abstract diagnostic store that
//! some stage within the compiler can implement.

use crate::report::Report;

pub trait Diagnostics<E: Into<Report>, W> {
    /// The store that is used to store the relevant diagnostics,
    /// this is up to the implementation of the trait how the  
    /// store is implemented.
    type DiagnosticsStore;

    /// Get a reference to the associated [Self::DiagnosticsStore]
    fn diagnostic_store(&self) -> &Self::DiagnosticsStore;

    /// Get a mutable reference to [Self::DiagnosticsStore]
    fn diagnostic_store_mut(&mut self) -> &mut Self::DiagnosticsStore;

    /// Add an error into the [Self]
    fn add_error(&mut self, error: E);

    /// Add a warning into the diagnostics store.
    fn add_warning(&mut self, warning: W);

    /// Check if the diagnostics has an error.
    fn has_errors(&self) -> bool;

    /// Check if the diagnostics has a warning
    fn has_warnings(&self) -> bool;

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
