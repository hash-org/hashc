//! Contains structures to store lists of arguments/parameters etc (any
//! name-indexed type).
use std::{borrow::Cow, cell::RefCell, collections::HashSet, fmt};

use hash_ast::ast::ParamOrigin;
use hash_source::identifier::Identifier;
use hash_utils::{
    new_sequence_store_key,
    store::{
        DefaultPartialStore, DefaultSequenceStore, PartialCloneStore, PartialStore, SequenceStore,
        SequenceStoreKey,
    },
};

use crate::old::{
    fmt::{ForFormatting, PrepareForFormatting},
    terms::TermId,
};

/// Trait to be implemented by primitives which contain a `name` field that is
/// an optional identifier.
pub trait GetNameOpt {
    /// Get the name of [Self], which should be an [`Option<Identifier>`].
    fn get_name_opt(&self) -> Option<Identifier>;
}

/// A borrowed or owned list of parameters, generic over the parameter type.
#[derive(Debug, Clone)]
pub struct ParamList<'p, ParamType: Clone> {
    params: Cow<'p, [ParamType]>,
    origin: ParamOrigin,
}

impl<ParamType: GetNameOpt + Clone> ParamList<'static, ParamType> {
    /// Create a new [ParamList] from the given vec of parameters and origin.
    pub fn new_owned(params: Vec<ParamType>, origin: ParamOrigin) -> Self {
        Self { params: Cow::Owned(params), origin }
    }
}

impl<'p, ParamType: GetNameOpt + Clone> ParamList<'p, ParamType> {
    /// Create a new [ParamList] from the given slice of parameters.
    pub fn new(params: &'p [ParamType], origin: ParamOrigin) -> Self {
        Self { params: Cow::Borrowed(params), origin }
    }

    /// Get the parameters as a positional slice
    pub fn positional(&self) -> &[ParamType] {
        self.params.as_ref()
    }

    /// Get the length of the parameters.
    pub fn len(&self) -> usize {
        self.params.len()
    }

    /// Borrow the parameters as a borrowed type.
    pub fn borrowed<'s: 'p>(&'s self) -> ParamList<'s, ParamType> {
        Self::new(self.params.as_ref(), self.origin)
    }

    /// Check if the [ParamList] is empty
    pub fn is_empty(&self) -> bool {
        self.params.is_empty()
    }

    /// Get the origin of the parameters.
    pub fn origin(&self) -> ParamOrigin {
        self.origin
    }

    /// Turn [Self] into the parameters as a positional vector.
    pub fn into_positional(self) -> Vec<ParamType> {
        self.params.into_owned()
    }

    /// Get a parameter by name.
    pub fn get_by_name(&self, name: Identifier) -> Option<(usize, &ParamType)> {
        self.params.iter().enumerate().find_map(|(i, param)| {
            if param.get_name_opt().contains(&name) {
                Some((i, param))
            } else {
                None
            }
        })
    }

    /// Get all the names of the fields within the [ParamList
    pub fn names(&self) -> HashSet<Identifier> {
        HashSet::from_iter(self.params.iter().flat_map(|param| param.get_name_opt()))
    }
}

/// A parameter, declaring a potentially named variable with a given type and
/// default value.
#[derive(Debug, Clone, Hash, Copy)]
pub struct Param {
    pub name: Option<Identifier>,
    pub ty: TermId,
    pub default_value: Option<TermId>,
}

impl GetNameOpt for Param {
    fn get_name_opt(&self) -> Option<Identifier> {
        self.name
    }
}

/// A list of parameters.
pub type Params<'p> = ParamList<'p, Param>;

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

/// Represents which kind of field is being accessed
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Field {
    Named(Identifier),
    Numeric(usize),
}

impl fmt::Display for Field {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Field::Named(name) => write!(f, "{name}"),
            Field::Numeric(index) => write!(f, "{index}"),
        }
    }
}

impl From<&str> for Field {
    fn from(index: &str) -> Self {
        Field::Named(index.into())
    }
}

impl From<Identifier> for Field {
    fn from(index: Identifier) -> Self {
        Field::Named(index)
    }
}

impl From<usize> for Field {
    fn from(ident: usize) -> Self {
        Field::Numeric(ident)
    }
}

/// The operator used to perform a member access.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessOp {
    /// The `::` accessor (namespace operator).
    ///
    /// Works for modules, traits, enums.
    Namespace,
    /// The `.` accessor (property operator).
    ///
    /// Works for structs, tuples.
    Property,
}

impl fmt::Display for AccessOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AccessOp::Namespace => write!(f, "namespace member"),
            AccessOp::Property => write!(f, "property"),
        }
    }
}

new_sequence_store_key!(pub ParamsId);
pub type ParamsStore = ParamListStore<ParamsId, Param>;

impl PrepareForFormatting for ParamsId {}

impl fmt::Display for ForFormatting<'_, ParamsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params_id = self.t;

        self.global_storage.params_store.map_as_param_list_fast(params_id, |params| {
            for (i, param) in params.positional().iter().enumerate() {
                match param.name {
                    Some(param_name) => {
                        write!(
                            f,
                            "{}: {}",
                            param_name,
                            param.ty.for_formatting(self.global_storage)
                        )?;
                    }
                    None => {
                        write!(f, "{}", param.ty.for_formatting(self.global_storage))?;
                    }
                }
                if i != params.len() - 1 {
                    write!(f, ", ")?;
                }
            }

            Ok(())
        })
    }
}
