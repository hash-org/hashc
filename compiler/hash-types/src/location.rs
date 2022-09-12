//! Map of various locations for data structures within the typechecker.
//! This map is used to store locations of terms, parameters, arguments
//! and declaration in one place rather than scattering them across the
//! entire implementation of the storage.

use std::{cell::RefCell, collections::HashMap, hash::Hash, rc::Rc};

use hash_source::location::{SourceLocation, Span};
use hash_utils::store::{DefaultPartialStore, PartialStore};

use crate::{
    arguments::ArgsId,
    params::ParamsId,
    pats::{PatArgsId, PatId},
    scope::ScopeId,
    terms::TermId,
};

/// An index into the location map.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum LocationTarget {
    /// A term.
    Term(TermId),
    /// A parameter key includes the parent [ParamsId] and an index to which
    /// parameter
    Param(ParamsId, usize),
    /// A argument key includes the parent [ArgsId] and an index to which
    /// argument
    Arg(ArgsId, usize),
    /// A declaration key includes the parent [ScopeId] and an index to which
    /// declaration
    Declaration(ScopeId, usize),
    /// A pattern parameter key includes the parent [PatArgsId] and an
    /// index to which parameter
    PatArg(PatArgsId, usize),
    /// A pattern.
    Pat(PatId),
    /// A location (no-op).
    Location(SourceLocation),
}

impl From<TermId> for LocationTarget {
    fn from(id: TermId) -> Self {
        Self::Term(id)
    }
}

impl<T: Clone> From<&T> for LocationTarget
where
    LocationTarget: From<T>,
{
    fn from(x: &T) -> Self {
        Self::from(x.clone())
    }
}

impl From<PatId> for LocationTarget {
    fn from(id: PatId) -> Self {
        Self::Pat(id)
    }
}

impl From<(ParamsId, usize)> for LocationTarget {
    fn from((id, index): (ParamsId, usize)) -> Self {
        Self::Param(id, index)
    }
}

impl From<(ArgsId, usize)> for LocationTarget {
    fn from((id, index): (ArgsId, usize)) -> Self {
        Self::Arg(id, index)
    }
}

impl From<(ScopeId, usize)> for LocationTarget {
    fn from((id, index): (ScopeId, usize)) -> Self {
        Self::Declaration(id, index)
    }
}

impl From<(PatArgsId, usize)> for LocationTarget {
    fn from((id, index): (PatArgsId, usize)) -> Self {
        Self::PatArg(id, index)
    }
}

impl From<SourceLocation> for LocationTarget {
    fn from(loc: SourceLocation) -> Self {
        Self::Location(loc)
    }
}

/// Types that paired with an index, create a [LocationTarget].
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum IndexedLocationTarget {
    Params(ParamsId),
    Args(ArgsId),
    Scope(ScopeId),
    PatArgs(PatArgsId),
}

impl From<ParamsId> for IndexedLocationTarget {
    fn from(id: ParamsId) -> Self {
        IndexedLocationTarget::Params(id)
    }
}

impl From<ArgsId> for IndexedLocationTarget {
    fn from(id: ArgsId) -> Self {
        IndexedLocationTarget::Args(id)
    }
}

impl From<PatArgsId> for IndexedLocationTarget {
    fn from(id: PatArgsId) -> Self {
        IndexedLocationTarget::PatArgs(id)
    }
}

impl From<ScopeId> for IndexedLocationTarget {
    fn from(id: ScopeId) -> Self {
        IndexedLocationTarget::Scope(id)
    }
}

impl From<(IndexedLocationTarget, usize)> for LocationTarget {
    fn from((target, i): (IndexedLocationTarget, usize)) -> Self {
        match target {
            IndexedLocationTarget::Params(params) => LocationTarget::Param(params, i),
            IndexedLocationTarget::Args(args) => LocationTarget::Arg(args, i),
            IndexedLocationTarget::PatArgs(params) => LocationTarget::PatArg(params, i),
            IndexedLocationTarget::Scope(scope) => LocationTarget::Declaration(scope, i),
        }
    }
}

/// Stores the source location of various targets in the AST tree.
///
/// Not every [LocationTarget] is guaranteed to have an attached location, but
/// if it does it will be stored here. The internal structure of the locations
/// is split into 4 different maps which contain mappings between the various
/// ids that are variants of [LocationTarget]. This is done so that the overhead
/// of copying locations is as small as possible (since copying can occur often
/// when ids are newly generated from either simplifications or substitutions).
///
/// When a set of locations (for example a [ParamsId]) is copied, the reference
/// to the map of locations that the internal parameters refer to is copied
/// since the inner map is behind an [Rc<T>].
#[derive(Debug, Default)]
pub struct LocationStore {
    /// A map between [TermId] to [SourceLocation]
    term_map: DefaultPartialStore<TermId, SourceLocation>,
    /// A map between [ParamsId] and all of the [SourceLocation]s indexed by the
    /// inner offset.
    param_map: DefaultPartialStore<ParamsId, Rc<RefCell<HashMap<usize, SourceLocation>>>>,
    /// A map between [ArgsId] and all of the [SourceLocation]s indexed by the
    /// inner offset.
    arg_map: DefaultPartialStore<ArgsId, Rc<RefCell<HashMap<usize, SourceLocation>>>>,
    /// A map between [ScopeId] and all of the [SourceLocation]s indexed by the
    /// inner offset.
    declaration_map: DefaultPartialStore<ScopeId, Rc<RefCell<HashMap<usize, SourceLocation>>>>,
    /// A map between [PatArgsId] and all of the [SourceLocation]s indexed
    /// by the inner offset.
    pat_arg_map: DefaultPartialStore<PatArgsId, Rc<RefCell<HashMap<usize, SourceLocation>>>>,
    /// A map between [PatId] to [SourceLocation]
    pat_map: DefaultPartialStore<PatId, SourceLocation>,
}

impl LocationStore {
    /// Create a new [LocationStore]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a [SourceLocation] to a specified [LocationTarget]
    pub fn add_location_to_target(
        &self,
        target: impl Into<LocationTarget>,
        location: SourceLocation,
    ) {
        macro_rules! add_indexed {
            ($map:expr, $value:expr, $index:expr) => {
                let map = {
                    if let Some(map) = $map.get($value) {
                        map
                    } else {
                        let new = Rc::new(RefCell::new(HashMap::new()));
                        $map.insert($value, new.clone());
                        new
                    }
                };
                map.borrow_mut().insert($index, location);
            };
        }
        match target.into() {
            LocationTarget::Term(term) => {
                self.term_map.insert(term, location);
            }
            LocationTarget::Param(param, index) => {
                add_indexed!(self.param_map, param, index);
            }
            LocationTarget::Arg(arg, index) => {
                add_indexed!(self.arg_map, arg, index);
            }
            LocationTarget::Declaration(scope, index) => {
                add_indexed!(self.declaration_map, scope, index);
            }
            LocationTarget::PatArg(pat_arg, index) => {
                add_indexed!(self.pat_arg_map, pat_arg, index);
            }
            LocationTarget::Pat(pat) => {
                self.pat_map.insert(pat, location);
            }
            _ => {
                // no-op
                log::warn!("Tried to set location on a LocationTarget::Location")
            }
        };
    }

    /// Get a [SourceLocation] from a specified [LocationTarget]
    pub fn get_location(&self, target: impl Into<LocationTarget>) -> Option<SourceLocation> {
        match target.into() {
            LocationTarget::Term(term) => self.term_map.get(term),
            LocationTarget::Param(param, index) => {
                Some(*self.param_map.get(param)?.borrow().get(&index)?)
            }
            LocationTarget::Arg(arg, index) => Some(*self.arg_map.get(arg)?.borrow().get(&index)?),
            LocationTarget::Declaration(scope, index) => {
                Some(*self.declaration_map.get(scope)?.borrow().get(&index)?)
            }
            LocationTarget::Pat(pat) => self.pat_map.get(pat),
            LocationTarget::PatArg(param_pat, index) => {
                Some(*self.pat_arg_map.get(param_pat)?.borrow().get(&index)?)
            }
            LocationTarget::Location(location) => Some(location),
        }
    }

    /// Get the associated [Span] with from the specified [LocationTarget]
    pub fn get_span(&self, target: impl Into<LocationTarget>) -> Option<Span> {
        self.get_location(target).map(|loc| loc.span)
    }

    /// Copy a set of locations from the first [IndexedLocationTarget] to the
    /// second [IndexedLocationTarget].
    pub fn copy_locations(
        &self,
        src: impl Into<IndexedLocationTarget> + Clone,
        dest: impl Into<IndexedLocationTarget> + Clone,
    ) {
        let src = src.into();
        let dest = dest.into();

        macro_rules! insert_dest {
            ($origin:expr) => {
                match dest {
                    IndexedLocationTarget::Params(dest) => {
                        self.param_map.insert(dest, $origin.clone());
                    }
                    IndexedLocationTarget::Args(dest) => {
                        self.arg_map.insert(dest, $origin.clone());
                    }
                    IndexedLocationTarget::PatArgs(dest) => {
                        self.pat_arg_map.insert(dest, $origin.clone());
                    }
                    IndexedLocationTarget::Scope(dest) => {
                        self.declaration_map.insert(dest, $origin.clone());
                    }
                }
            };
        }

        match src {
            IndexedLocationTarget::Params(src) => {
                if let Some(origin) = self.param_map.get(src) {
                    insert_dest!(origin);
                }
            }
            IndexedLocationTarget::Args(src) => {
                if let Some(origin) = self.arg_map.get(src) {
                    insert_dest!(origin);
                }
            }
            IndexedLocationTarget::PatArgs(src) => {
                if let Some(origin) = self.pat_arg_map.get(src) {
                    insert_dest!(origin);
                }
            }
            IndexedLocationTarget::Scope(src) => {
                if let Some(origin) = self.declaration_map.get(src) {
                    insert_dest!(origin);
                }
            }
        }
    }

    /// Copy a location from a source [LocationTarget] to a destination target.
    ///
    /// if the `source` is not present within the store, then no location is
    /// copied.
    pub fn copy_location(&self, src: impl Into<LocationTarget>, dest: impl Into<LocationTarget>) {
        if let Some(origin) = self.get_location(src.into()) {
            self.add_location_to_target(dest.into(), origin);
        }
    }

    /// Merge the given [LocationTarget]s into a single [LocationTarget]
    /// provided that they can be merged in terms of order. All `ids` of the
    /// [SourceLocation]s must match.
    ///
    /// **Note**: At least one of the [LocationTarget]s must have an associated
    /// [SourceLocation].
    pub fn merge_locations(
        &self,
        locations: impl Iterator<Item = LocationTarget>,
    ) -> LocationTarget {
        let mut locations = locations.skip_while(|loc| self.get_location(loc).is_none());
        let mut initial_span = locations.next().map(|loc| self.get_location(loc).unwrap()).unwrap();

        // Iterate over the locations and then join them with the initial one
        for location in locations {
            if let Some(other) = self.get_location(location) {
                initial_span = initial_span.join(other);
            }
        }

        initial_span.into()
    }
}
