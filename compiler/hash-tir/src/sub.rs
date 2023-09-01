//! Definitions related to substitutions.
use std::fmt::{self, Display, Formatter};

use hash_utils::smallvec::SmallVec;

use crate::{environment::env::WithEnv, symbols::SymbolId, terms::TermId};

/// An entry in a substitution.
///
/// This is a pair of a subject and a term to replace the subject with.
#[derive(Debug, Clone, Copy)]
pub struct SubEntry {
    pub from: SymbolId,
    pub to: TermId,
}

/// A substitution, which replaces variables in terms, by other terms.
#[derive(Debug, Clone)]
pub struct Sub {
    data: SmallVec<[SubEntry; 3]>,
}

impl Sub {
    /// Create an empty substitution.
    pub fn identity() -> Self {
        Self { data: SmallVec::new() }
    }

    /// Create a substitution from pairs of ([`SubSubject`], [`TermId`]).
    pub fn from_pairs(pairs: impl IntoIterator<Item = (SymbolId, TermId)>) -> Self {
        Self { data: pairs.into_iter().map(|(from, to)| SubEntry { from, to }).collect() }
    }

    /// Get the substitution for the given [`SubSubject`], if any.
    pub fn get_sub_for(&self, subject: SymbolId) -> Option<TermId> {
        self.data.iter().find(|entry| entry.from == subject).map(|entry| entry.to)
    }

    /// Get the substitution for the given [`Symbol`] corresponding to a
    /// variable or a hole, if any.
    pub fn get_sub_for_var_or_hole(&self, subject: SymbolId) -> Option<TermId> {
        self.data.iter().find(|entry| entry.from == subject).map(|entry| entry.to)
    }

    /// Get all the subjects (i.e. the domain) of the substitution as an
    /// iterator.
    pub fn domain(&self) -> impl Iterator<Item = SymbolId> + '_ {
        self.data.iter().map(|entry| entry.from)
    }

    /// Get all the targets (i.e. the range) of the substitution as an iterator.
    pub fn range(&self) -> impl Iterator<Item = TermId> + '_ {
        self.data.iter().map(|entry| entry.to)
    }

    /// Get the pairs of the substitution as an iterator.
    pub fn iter(&self) -> impl Iterator<Item = (SymbolId, TermId)> + '_ {
        self.data.iter().map(|entry| (entry.from, entry.to))
    }

    /// Whether the substitution is empty (i.e. identity).
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Get the number of substitutions.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Add a variable substitution.
    pub fn insert(&mut self, from: SymbolId, to: TermId) {
        self.data.push(SubEntry { from, to })
    }

    /// Add variable substitutions from the given [`Sub`].
    ///
    /// @@Todo: apply to current substitution first
    pub fn extend(&mut self, other: &Sub) {
        self.data.extend(other.data.iter().copied())
    }

    /// Join two substitutions.
    pub fn join(mut self, other: &Sub) -> Sub {
        self.extend(other);
        self
    }

    /// Add variable substitutions from the iterator of pairs.
    pub fn extend_from_pairs(&mut self, pairs: impl IntoIterator<Item = (SymbolId, TermId)>) {
        self.data.extend(pairs.into_iter().map(|(from, to)| SubEntry { from, to }))
    }

    /// Remove the substitution for the given variable.
    pub fn remove(&mut self, from: SymbolId) -> Option<TermId> {
        self.data.iter().position(|entry| entry.from == from).map(|i| self.data.swap_remove(i).to)
    }

    /// Clear the substitution. (i.e. make it identity)
    pub fn clear_diagnostics(&mut self) {
        self.data.clear()
    }
}

impl Default for Sub {
    fn default() -> Self {
        Self::identity()
    }
}

impl Display for WithEnv<'_, &Sub> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (from, to)) in self.value.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{} ~> {}", from, to)?;
        }
        write!(f, "}}")
    }
}
