//! Definitions related to substitutions.
use derive_more::From;
use hash_types::new::{holes::Hole, symbols::Symbol, terms::TermId};
use smallvec::SmallVec;

/// The subject of a substitution
///
/// This is either a symbolic variable, or hole.
#[derive(Debug, Clone, Copy, PartialEq, Eq, From)]
pub enum SubSubject {
    /// A variable subject.
    ///
    /// For example, ((x) => x)(3) will form the substitution x ~> 3
    Var(Symbol),
    /// A hole subject.
    ///
    /// For example, x := 3, where x: U1, will form the substitution U1 ~> i32
    Hole(Hole),
}

impl PartialEq<Symbol> for SubSubject {
    fn eq(&self, other: &Symbol) -> bool {
        match self {
            SubSubject::Var(s) => s == other,
            SubSubject::Hole(_) => false,
        }
    }
}

impl PartialEq<Hole> for SubSubject {
    fn eq(&self, other: &Hole) -> bool {
        match self {
            SubSubject::Var(_) => false,
            SubSubject::Hole(h) => h == other,
        }
    }
}

/// An entry in a substitution.
///
/// This is a pair of a subject and a term to replace the subject with.
#[derive(Debug, Clone, Copy)]
pub struct SubEntry {
    pub from: SubSubject,
    pub to: TermId,
}

/// A substitution, which replaces variables in terms, by other terms.
#[derive(Debug, Clone)]
pub struct Sub {
    data: SmallVec<[SubEntry; 4]>,
}

impl Sub {
    /// Create an empty substitution.
    pub fn identity() -> Self {
        Self { data: SmallVec::new() }
    }

    /// Create a substitution from pairs of ([`SubSubject`], [`TermId`]).
    pub fn from_pairs(pairs: impl IntoIterator<Item = (SubSubject, TermId)>) -> Self {
        Self { data: pairs.into_iter().map(|(from, to)| SubEntry { from, to }).collect() }
    }

    /// Get the substitution for the given [`SubSubject`], if any.
    pub fn get_sub_for(&self, subject: impl Into<SubSubject>) -> Option<TermId> {
        let subject = subject.into();
        self.data.iter().find(|entry| entry.from == subject).map(|entry| entry.to)
    }

    /// Get all the subjects (i.e. the domain) of the substitution as an
    /// iterator.
    pub fn domain(&self) -> impl Iterator<Item = SubSubject> + '_ {
        self.data.iter().map(|entry| entry.from)
    }

    /// Get all the targets (i.e. the range) of the substitution as an iterator.
    pub fn range(&self) -> impl Iterator<Item = TermId> + '_ {
        self.data.iter().map(|entry| entry.to)
    }

    /// Get the pairs of the substitution as an iterator.
    pub fn iter(&self) -> impl Iterator<Item = (SubSubject, TermId)> + '_ {
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
    pub fn insert(&mut self, from: impl Into<SubSubject>, to: TermId) {
        let from = from.into();
        self.data.push(SubEntry { from, to })
    }

    /// Add variable substitutions from the given [`Sub`].
    pub fn extend(&mut self, other: &Sub) {
        self.data.extend(other.data.iter().copied())
    }

    /// Add variable substitutions from the iterator of pairs.
    pub fn extend_from_pairs(&mut self, pairs: impl IntoIterator<Item = (SubSubject, TermId)>) {
        self.data.extend(pairs.into_iter().map(|(from, to)| SubEntry { from, to }))
    }

    /// Remove the substitution for the given variable.
    pub fn remove(&mut self, from: impl Into<SubSubject>) -> Option<TermId> {
        let from = from.into();
        self.data.iter().position(|entry| entry.from == from).map(|i| self.data.swap_remove(i).to)
    }

    /// Clear the substitution. (i.e. make it identity)
    pub fn clear(&mut self) {
        self.data.clear()
    }
}

impl Default for Sub {
    fn default() -> Self {
        Self::identity()
    }
}
