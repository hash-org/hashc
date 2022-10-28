use hash_utils::{new_store_key, store::DefaultStore};

use crate::{
    data::DataDefId, defs::DefArgsId, params::ParamsId, refs::RefTy, terms::TermId,
    trts::TrtBoundsId,
};

#[derive(Debug, Clone, Copy)]
pub struct FnTy {
    pub implicit: bool,
    pub pure: bool,
    pub params: ParamsId,
    pub conditions: ParamsId,
    pub return_type: TyId,
}

#[derive(Debug, Clone, Copy)]
pub struct TupleTy {
    pub data: ParamsId,
    pub conditions: ParamsId,
}

#[derive(Debug, Clone, Copy)]
pub struct UnionTy {
    pub variants: ParamsId,
}

/// The type of types, i.e. a universe.
#[derive(Debug, Clone, Copy)]
pub struct TypeTy {
    /// Whether this is a small universe or a large one.
    ///
    /// Small universe does not include `Meta(..)` and `Type(..)`, where as a
    /// large one does.
    pub small: bool,
    /// Any additional bounds that types in the universe must satisfy.
    pub trait_bounds: TrtBoundsId,
}

/// The type of a meta construct, i.e. a type which cannot be given by the user.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaTy {
    /// The type of any `mod/impl (...args) {...}` definition
    ModTy,
    /// The type of any `trait (...args) {...}` definition
    TraitTy,
    /// The type of any `datatype (...args) {...}` definition,
    ///
    /// If the `args` of the data-type in question is empty, then its type is
    /// coercible to `Type`. Otherwise, once the `args` of the datatype are
    /// given, its type is coercible to `Type`.
    DataDefTy,
}

/// A type pointing to a data-type definition.
#[derive(Debug, Clone, Copy)]
pub struct DataTy {
    pub data_def: DataDefId,
    pub args: DefArgsId,
}

#[derive(Debug, Clone, Copy)]
pub enum Ty {
    Expr(TermId),
    Union(UnionTy),
    Tuple(TupleTy),
    Fn(FnTy),
    Data(DataTy),
    Type(TypeTy),
    Meta(MetaTy),
    Ref(RefTy),
}

new_store_key!(pub TyId);
pub type TyStore = DefaultStore<TyId, Ty>;
