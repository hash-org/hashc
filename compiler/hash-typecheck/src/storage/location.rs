//! Map of various locations for data structures within the typechecker.
//! This map is used to store locations of terms, parameters, arguments
//! and declaration in one place rather than scattering them across the
//! entire implementation of the storage.

use std::collections::HashMap;

use hash_source::location::SourceLocation;

use super::primitives::{ArgsId, ParamsId, ScopeId, TermId};

/// An index into the location map.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum LocationTarget {
    Term(TermId),
    Params(ParamsId, usize),
    Args(ArgsId, usize),
    Declaration(ScopeId, usize),
}

/// Stores the source location of various targets in the AST tree.
///
/// Not every [LocationTarget] is guaranteed to have an attached location, but
/// if it does it will be stored here.
#[derive(Debug, Default)]
pub struct LocationStore {
    data: HashMap<LocationTarget, SourceLocation>,
}

impl LocationStore {
    /// Create a new [LocationStore]
    pub fn new() -> Self {
        Self { data: HashMap::new() }
    }

    /// Add a [SourceLocation] to a specified [LocationTarget]
    pub fn add_location_to_target(&mut self, target: LocationTarget, location: SourceLocation) {
        self.data.insert(target, location);
    }

    /// Get a [SourceLocation] from a specified [LocationTarget]
    pub fn get_location(&self, target: LocationTarget) -> Option<SourceLocation> {
        self.data.get(&target).copied()
    }

    /// Copy a location from a source [LocationTarget] to a destination target.
    ///
    /// if the `source` is not present within the store, then no location is
    /// copied.
    pub fn copy_location(&mut self, src: LocationTarget, dest: LocationTarget) {
        if let Some(origin) = self.get_location(src) {
            self.add_location_to_target(dest, origin);
        }
    }
}

impl From<TermId> for LocationTarget {
    fn from(id: TermId) -> Self {
        Self::Term(id)
    }
}

impl From<&TermId> for LocationTarget {
    fn from(id: &TermId) -> Self {
        Self::Term(*id)
    }
}

impl From<(ParamsId, usize)> for LocationTarget {
    fn from((id, index): (ParamsId, usize)) -> Self {
        Self::Params(id, index)
    }
}
