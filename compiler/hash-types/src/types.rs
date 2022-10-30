use hash_utils::{new_store_key, store::DefaultStore};

use crate::{
    data::DataTy, fns::FnTy, refs::RefTy, terms::TermId, trts::TrtBoundsId, tuples::TupleTy,
    unions::UnionTy,
};

/// The type of types, i.e. a universe.
#[derive(Debug, Clone, Copy)]
pub struct TypeTy {
    /// Whether this is a small universe or a large one.
    ///
    /// A small universe does not include `Meta(..)` and `Type(..)`, where as a
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

/// Represents a type in a Hash program.
#[derive(Debug, Clone, Copy)]
pub enum Ty {
    /// A term which evaluates to a type.
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
