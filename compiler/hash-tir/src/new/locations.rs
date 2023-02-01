use std::cell::RefCell;

use bimap::BiMap;
use hash_source::location::{SourceLocation, Span};
use hash_utils::store::SequenceStoreKey;

use super::{
    args::{ArgId, ArgsId, PatArgId, PatArgsId},
    data::{CtorDefId, CtorDefsId, DataDefId},
    fns::FnDefId,
    mods::{ModDefId, ModMemberId, ModMembersId},
    params::{ParamId, ParamsId},
    scopes::{StackId, StackMemberId},
    symbols::Symbol,
    terms::TermId,
    tys::TyId,
};

macro_rules! location_targets {
    ($($name:ident: $ty:ty $(= sequence $indexed_name:ident: $indexed_type:ident)?),* $(,)?) => {
        #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
        pub enum LocationTarget {
           $(
               $name($ty),
           )*
           Location(SourceLocation),
        }

        #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
        pub enum IndexedLocationTarget {
            $(
                $(
                    $indexed_name($indexed_type),
                )?
            )*
        }

        impl hash_utils::store::SequenceStoreKey for IndexedLocationTarget {
            fn to_index_and_len(self) -> (usize, usize) {
                match self {
                    $(
                        $(
                            Self::$indexed_name(id) => id.to_index_and_len(),
                        )?
                    )*
                }
            }

            fn from_index_and_len_unchecked(_: usize, _: usize) -> Self {
                // Invalid because IndexedLocationTarget is one of potentially many different types
                // of indexed targets
                panic!("Used from_index_and_len_unchecked in indexed location target")
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

        impl From<SourceLocation> for LocationTarget {
            fn from(loc: SourceLocation) -> Self {
                Self::Location(loc)
            }
        }

        $(
            impl From<$ty> for LocationTarget {
                fn from(ty: $ty) -> Self {
                    Self::$name(ty)
                }
            }
        )*

        $(
            $(
                impl From<$indexed_type> for IndexedLocationTarget {
                    fn from(ty: $indexed_type) -> Self {
                        Self::$indexed_name(ty)
                    }
                }
            )?
        )*

        impl From<(IndexedLocationTarget, usize)> for LocationTarget {
            fn from((ty, index): (IndexedLocationTarget, usize)) -> Self {
                match ty {
                    $(
                        $(
                            IndexedLocationTarget::$indexed_name(indexed_target) => Self::$name((indexed_target, index)),
                        )?
                    )*
                }
            }
        }
    };
}

location_targets! {
    Term: TermId,
    Ty: TyId,
    Symbol: Symbol,

    DataDef: DataDefId,
    CtorDef: CtorDefId = sequence CtorDefs: CtorDefsId,

    ModDef: ModDefId,
    ModMember: ModMemberId = sequence ModMembers: ModMembersId,

    Stack: StackId,
    StackMember: StackMemberId,

    FnDef: FnDefId,

    Arg: ArgId = sequence Args: ArgsId,
    Param: ParamId = sequence Params: ParamsId,
    PatArg: PatArgId = sequence PatArgs: PatArgsId,
}

/// Stores the source location of various targets in the term tree.
///
/// Not every [LocationTarget] is guaranteed to have an attached location, but
/// if it does it will be stored here.
///
/// When a set of locations (for example a [ParamsId]) is copied, the reference
/// to the map of locations that the internal parameters refer to is copied
/// since the inner map is behind an [Rc<T>].
#[derive(Debug, Default)]
pub struct LocationStore {
    data: RefCell<BiMap<LocationTarget, SourceLocation>>,
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
        self.data.borrow_mut().insert(target.into(), location);
    }

    /// Add a set of [SourceLocation]s to a specified [IndexedLocationTarget]
    pub fn add_locations_to_targets(
        &self,
        targets: impl Into<IndexedLocationTarget>,
        location: impl Fn(usize) -> Option<SourceLocation>,
    ) {
        let targets = targets.into();
        for target in targets.to_index_range() {
            if let Some(loc) = location(target) {
                self.add_location_to_target(LocationTarget::from((targets, target)), loc);
            }
        }
    }

    /// Get a [SourceLocation] from a specified [LocationTarget]
    pub fn get_location(&self, target: impl Into<LocationTarget>) -> Option<SourceLocation> {
        self.data.borrow().get_by_left(&target.into()).copied()
    }

    /// Get the associated [Span] with from the specified [LocationTarget]
    pub fn get_span(&self, target: impl Into<LocationTarget>) -> Option<Span> {
        self.get_location(target).map(|loc| loc.span)
    }

    /// Get the overall [Span] covering all the members of a specified
    /// [IndexedLocationTarget].
    pub fn get_overall_span(&self, target: impl Into<IndexedLocationTarget>) -> Option<Span> {
        let target = target.into();
        target
            .to_index_range()
            .map(|index| self.get_span(LocationTarget::from((target, index))))
            .fold(None, |acc, span| Some(acc?.join(span?)))
    }

    /// Get the overall [SourceLocation] covering all the members of a specified
    /// [IndexedLocationTarget].
    pub fn get_overall_location(
        &self,
        target: impl Into<IndexedLocationTarget>,
    ) -> Option<SourceLocation> {
        let target = target.into();
        target
            .to_index_range()
            .map(|index| self.get_location(LocationTarget::from((target, index))))
            .fold(None, |acc, loc| Some(acc?.join(loc?)))
    }

    /// Copy a set of locations from the first [IndexedLocationTarget] to the
    /// second [IndexedLocationTarget].
    ///
    /// Both [IndexedLocationTarget]s must have the same length.
    pub fn copy_locations(
        &self,
        src: impl Into<IndexedLocationTarget> + Clone,
        dest: impl Into<IndexedLocationTarget> + Clone,
    ) {
        let src = src.into();
        let dest = dest.into();
        for index in src.to_index_range() {
            self.copy_location((src, index), (dest, index));
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
