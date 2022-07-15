//! Map of various locations for data structures within the typechecker.
//! This map is used to store locations of terms, parameters, arguments
//! and declaration in one place rather than scattering them across the
//! entire implementation of the storage.

use std::{cell::RefCell, collections::HashMap, hash::Hash, rc::Rc};

use hash_source::location::SourceLocation;

use super::primitives::{ArgsId, ParamsId, PatternId, PatternParamsId, ScopeId, TermId};

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
    /// A pattern parameter key includes the parent [ParamsPatternId] and an
    /// index to which parameter
    ParamPattern(PatternParamsId, usize),
    /// A pattern.
    Pattern(PatternId),
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
///
/// @@Future: It would be nice to have some equivalent map but also indexed by
/// [SourceId]. Although, this might be complicated to implement as shared data
/// structures like [Params] might have multiple [SourceId]s.
#[derive(Debug, Default)]
pub struct LocationStore {
    /// A map between [TermId] to [SourceLocation]
    term_map: HashMap<TermId, SourceLocation>,
    /// A map between [ParamsId] and all of the [SourceLocation]s indexed by the
    /// inner offset.
    param_map: HashMap<ParamsId, Rc<RefCell<HashMap<usize, SourceLocation>>>>,
    /// A map between [ArgsId] and all of the [SourceLocation]s indexed by the
    /// inner offset.
    arg_map: HashMap<ArgsId, Rc<RefCell<HashMap<usize, SourceLocation>>>>,
    /// A map between [ScopeId] and all of the [SourceLocation]s indexed by the
    /// inner offset.
    declaration_map: HashMap<ScopeId, Rc<RefCell<HashMap<usize, SourceLocation>>>>,
    /// A map between [ParamPatternsId] and all of the [SourceLocation]s indexed
    /// by the inner offset.
    param_pattern_map: HashMap<PatternParamsId, Rc<RefCell<HashMap<usize, SourceLocation>>>>,
    /// A map between [PatternId] to [SourceLocation]
    pattern_map: HashMap<PatternId, SourceLocation>,
}

impl LocationStore {
    /// Create a new [LocationStore]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a [SourceLocation] to a specified [LocationTarget]
    pub fn add_location_to_target(
        &mut self,
        target: impl Into<LocationTarget>,
        location: SourceLocation,
    ) {
        match target.into() {
            LocationTarget::Term(term) => {
                self.term_map.insert(term, location);
            }
            LocationTarget::Param(param, index) => {
                let map = self
                    .param_map
                    .entry(param)
                    .or_insert_with(|| Rc::new(RefCell::new(HashMap::new())));
                map.borrow_mut().insert(index, location);
            }
            LocationTarget::Arg(arg, index) => {
                let map = self
                    .arg_map
                    .entry(arg)
                    .or_insert_with(|| Rc::new(RefCell::new(HashMap::new())));
                map.borrow_mut().insert(index, location);
            }
            LocationTarget::Declaration(scope, index) => {
                let map = self
                    .declaration_map
                    .entry(scope)
                    .or_insert_with(|| Rc::new(RefCell::new(HashMap::new())));
                map.borrow_mut().insert(index, location);
            }
            LocationTarget::ParamPattern(param_pattern, index) => {
                let map = self
                    .param_pattern_map
                    .entry(param_pattern)
                    .or_insert_with(|| Rc::new(RefCell::new(HashMap::new())));
                map.borrow_mut().insert(index, location);
            }
            LocationTarget::Pattern(pattern) => {
                self.pattern_map.insert(pattern, location);
            }
        };
    }

    /// Get a [SourceLocation] from a specified [LocationTarget]
    pub fn get_location(&self, target: impl Into<LocationTarget>) -> Option<SourceLocation> {
        match target.into() {
            LocationTarget::Term(term) => self.term_map.get(&term).copied(),
            LocationTarget::Param(param, index) => {
                Some(*self.param_map.get(&param)?.borrow().get(&index)?)
            }
            LocationTarget::Arg(arg, index) => Some(*self.arg_map.get(&arg)?.borrow().get(&index)?),
            LocationTarget::Declaration(scope, index) => {
                Some(*self.declaration_map.get(&scope)?.borrow().get(&index)?)
            }
            LocationTarget::Pattern(pattern) => self.pattern_map.get(&pattern).copied(),
            LocationTarget::ParamPattern(param_pattern, index) => {
                Some(*self.param_pattern_map.get(&param_pattern)?.borrow().get(&index)?)
            }
        }
    }

    /// Copy a parameter set within [LocationStore]. This will copy the internal
    /// reference of the src [ParamsId] to the `dest` [ParamsId]. This does not
    /// create a new separate copy of locations.
    pub fn copy_params_locations(&mut self, src: ParamsId, dest: ParamsId) {
        if let Some(origin) = self.param_map.get(&src) {
            self.param_map.insert(dest, origin.clone());
        }
    }

    /// Copy a arguments set within [LocationStore]. This will copy the internal
    /// reference of the src [ArgsId] to the `dest` [ArgsId]. This does not
    /// create a new separate copy of locations.
    pub fn copy_args_locations(&mut self, src: ArgsId, dest: ArgsId) {
        if let Some(origin) = self.arg_map.get(&src) {
            self.arg_map.insert(dest, origin.clone());
        }
    }

    /// Copy a declaration set within [LocationStore]. This will copy the
    /// internal reference of the src [ScopeId] to the `dest` [ScopeId].
    /// This does not create a new separate copy of locations.
    pub fn copy_declarations_locations(&mut self, src: ScopeId, dest: ScopeId) {
        if let Some(origin) = self.declaration_map.get(&src) {
            self.declaration_map.insert(dest, origin.clone());
        }
    }

    /// Copy a location from a source [LocationTarget] to a destination target.
    ///
    /// if the `source` is not present within the store, then no location is
    /// copied.
    pub fn copy_location(
        &mut self,
        src: impl Into<LocationTarget>,
        dest: impl Into<LocationTarget>,
    ) {
        if let Some(origin) = self.get_location(src.into()) {
            self.add_location_to_target(dest.into(), origin);
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
