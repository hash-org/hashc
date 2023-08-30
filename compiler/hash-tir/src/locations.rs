use std::collections::HashMap;

use hash_source::location::Span;
use hash_storage::store::SequenceStoreKey;
use hash_utils::parking_lot::RwLock;

use super::{
    args::{ArgId, PatArgId},
    data::{CtorDefId, DataDefId},
    fns::FnDefId,
    mods::{ModDefId, ModMemberId},
    params::ParamId,
    pats::PatId,
    scopes::{StackId, StackMemberId},
    symbols::Symbol,
    terms::TermId,
    tys::TyId,
};
use crate::{
    args::{ArgsSeqId, PatArgsSeqId},
    data::CtorDefsSeqId,
    mods::ModMembersSeqId,
    params::ParamsSeqId,
};

macro_rules! location_targets {
    ($($name:ident: $ty:ty $(= sequence $indexed_name:ident: $indexed_type:ident)?),* $(,)?) => {
        #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
        pub enum LocationTarget {
           $(
               $name($ty),
           )*
           Location(Span),
        }

        #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
        pub enum IndexedLocationTarget {
            $(
                $(
                    $indexed_name($indexed_type),
                )?
            )*
        }

        impl hash_storage::store::SequenceStoreKey for IndexedLocationTarget {
            type ElementKey = (Self, usize);
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

        impl From<Span> for LocationTarget {
            fn from(loc: Span) -> Self {
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
                            IndexedLocationTarget::$indexed_name(indexed_target) => Self::$name((indexed_target, index).into()),
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
    Pat: PatId,
    Symbol: Symbol,

    DataDef: DataDefId,
    CtorDef: CtorDefId = sequence CtorDefs: CtorDefsSeqId,

    ModDef: ModDefId,
    ModMember: ModMemberId = sequence ModMembers: ModMembersSeqId,

    Stack: StackId,
    StackMember: StackMemberId,

    FnDef: FnDefId,

    Arg: ArgId = sequence Args: ArgsSeqId,
    Param: ParamId = sequence Params: ParamsSeqId,
    PatArg: PatArgId = sequence PatArgs: PatArgsSeqId,
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
    // @@Performance: DashMap?
    data: RwLock<HashMap<LocationTarget, Span>>,
}

impl LocationStore {
    /// Create a new [LocationStore]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a [Span] to a specified [LocationTarget]
    pub fn add_location_to_target(&self, target: impl Into<LocationTarget>, location: Span) {
        self.data.write().insert(target.into(), location);
    }

    /// Add a set of [Span]s to a specified [IndexedLocationTarget]
    pub fn add_locations_to_targets(
        &self,
        targets: impl Into<IndexedLocationTarget>,
        location: impl Fn(usize) -> Option<Span>,
    ) {
        let targets = targets.into();
        for target in targets.to_index_range() {
            if let Some(loc) = location(target) {
                self.add_location_to_target(LocationTarget::from((targets, target)), loc);
            }
        }
    }

    /// Get a [Span] from a specified [LocationTarget]
    pub fn get_location(&self, target: impl Into<LocationTarget>) -> Option<Span> {
        self.data.read().get(&target.into()).copied()
    }

    /// Get the overall [Span] covering all the members of a specified
    /// [IndexedLocationTarget].
    pub fn get_overall_location(&self, target: impl Into<IndexedLocationTarget>) -> Option<Span> {
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
    /// [Span]s must match.
    ///
    /// **Note**: At least one of the [LocationTarget]s must have an associated
    /// [Span].
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
