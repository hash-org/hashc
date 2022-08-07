//! Contains structures to store lists of arguments/parameters etc (any
//! name-indexed type).
use hash_ast::ast::ParamOrigin;
use hash_source::identifier::Identifier;
use hash_utils::store::{
    DefaultPartialStore, DefaultSequenceStore, PartialStore, SequenceStore, SequenceStoreKey,
};
use std::{cell::RefCell, collections::HashSet};

use super::primitives::{GetNameOpt, ParamList};

/// A store that contains parameter lists, indexed by a generic key.
///
/// Also stores [ParamOrigin] for each parameter list.
#[derive(Debug)]
pub struct ParamListStore<ParamListKey, ParamType> {
    data: DefaultSequenceStore<ParamListKey, ParamType>,
    origins: DefaultPartialStore<ParamListKey, ParamOrigin>,
}

impl<ParamListKey, ParamType> Default for ParamListStore<ParamListKey, ParamType> {
    fn default() -> Self {
        Self { data: Default::default(), origins: Default::default() }
    }
}

impl<ParamListKey: SequenceStoreKey, ParamType: Clone> SequenceStore<ParamListKey, ParamType>
    for ParamListStore<ParamListKey, ParamType>
{
    fn internal_data(&self) -> &RefCell<Vec<ParamType>> {
        self.data.internal_data()
    }
}

impl<ParamListKey: SequenceStoreKey, ParamType: GetNameOpt + Clone>
    ParamListStore<ParamListKey, ParamType>
{
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the origin of the given parameters
    pub fn set_origin(&self, key: ParamListKey, origin: ParamOrigin) {
        self.origins.insert(key, origin);
    }

    /// Get the origin of the given parameters
    pub fn get_origin(&self, key: ParamListKey) -> ParamOrigin {
        self.origins.get(key).unwrap_or(ParamOrigin::Unknown)
    }

    /// Get a parameter by name.
    pub fn get_by_name(&self, key: ParamListKey, name: Identifier) -> Option<(usize, ParamType)> {
        self.map_as_param_list_fast(key, |list| list.get_by_name(name).map(|(i, p)| (i, p.clone())))
    }

    /// Get the given parameters as an owned [ParamList].
    pub fn get_owned_param_list(&self, key: ParamListKey) -> ParamList<'static, ParamType> {
        let origin = self.get_origin(key);
        ParamList::new_owned(self.get_vec(key), origin)
    }

    /// Get all the names of the given parameters as a hash set.
    pub fn names(&self, key: ParamListKey) -> HashSet<Identifier> {
        self.map_as_param_list_fast(key, |list| list.names())
    }

    /// Map a parameter sequence as a [ParamList].
    ///
    /// *Warning*: Same warning applies as with other `_fast` methods.
    pub fn map_as_param_list_fast<T>(
        &self,
        key: ParamListKey,
        f: impl FnOnce(ParamList<ParamType>) -> T,
    ) -> T {
        let origin = self.get_origin(key);
        self.data.map_fast(key, |value| {
            let param_list = ParamList::new(value, origin);
            f(param_list)
        })
    }

    /// Map a parameter sequence as a [ParamList].
    pub fn map_as_param_list<T>(
        &self,
        key: ParamListKey,
        f: impl FnOnce(ParamList<ParamType>) -> T,
    ) -> T {
        let origin = self.get_origin(key);
        self.data.map(key, |value| {
            let param_list = ParamList::new(value, origin);
            f(param_list)
        })
    }
}
