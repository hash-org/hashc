//! Definitions related to parameters to data types, functions, etc.
use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_source::identifier::Identifier;
use hash_storage::{
    static_sequence_store_direct,
    store::{
        statics::{SequenceStoreValue, StoreId},
        SequenceStore, SequenceStoreKey, TrivialSequenceStoreKey,
    },
};
use hash_utils::itertools::Itertools;

use super::{
    args::{ArgsId, PatArgsId},
    locations::IndexedLocationTarget,
    terms::TermId,
};
use crate::{
    args::SomeArgsId,
    context::ScopeKind,
    data::{CtorDefId, DataDefId},
    environment::stores::tir_stores,
    fns::{FnDefId, FnTy},
    symbols::Symbol,
    tir_debug_value_of_sequence_store_element_id,
    tuples::TupleTy,
    tys::{Ty, TyId},
};

/// A parameter, declaring a potentially named variable with a given type and
/// possibly a default value.
#[derive(Debug, Clone, Copy)]
pub struct Param {
    /// The name of the parameter.
    pub name: Symbol,
    /// The type of the parameter.
    pub ty: TyId,
    /// The default value of the parameter.
    pub default: Option<TermId>,
}

impl Param {
    /// Create a new parameter list with the given names, and holes for all
    /// types.
    pub fn seq_from_names_with_hole_types(param_names: impl Iterator<Item = Symbol>) -> ParamsId {
        Param::seq(
            param_names
                .map(|name| move |_id| Param { name, ty: Ty::hole(), default: None })
                .collect_vec(),
        )
    }

    /// Create a new parameter list with the given argument names, and holes for
    /// all types, and no default values.
    pub fn seq_from_args_with_hole_types(args: impl Into<SomeArgsId>) -> ParamsId {
        let args: SomeArgsId = args.into();
        Param::seq_from_names_with_hole_types(args.iter().map(|arg| arg.into_name()))
    }

    pub fn seq_positional(tys: impl IntoIterator<Item = TyId>) -> ParamsId {
        Param::seq_data(
            tys.into_iter()
                .map(|ty| Param { name: Symbol::fresh(), ty, default: None })
                .collect_vec(),
        )
    }

    pub fn name_ident(&self) -> Option<Identifier> {
        self.name.borrow().name
    }
}

impl ParamId {
    pub fn as_param_index(&self) -> ParamIndex {
        let name_sym = self.borrow().name.borrow();
        name_sym.name.map(ParamIndex::Name).unwrap_or(ParamIndex::Position(self.1))
    }
}

impl ParamsId {
    // Get the actual numerical parameter index from a given [ParamsId] and
    // [ParamIndex].
    pub fn at_param_index(&self, index: ParamIndex) -> Option<usize> {
        match index {
            ParamIndex::Name(name) => self.iter().enumerate().find_map(|(i, param)| {
                if param.borrow().name.borrow().name? == name {
                    Some(i)
                } else {
                    None
                }
            }),
            ParamIndex::Position(pos) => Some(pos),
        }
    }
}

static_sequence_store_direct!(
    store = pub ParamsStore,
    id = pub ParamsId[ParamId],
    value = Param,
    store_name = params,
    store_source = tir_stores()
);

tir_debug_value_of_sequence_store_element_id!(ParamId);

/// An index of a parameter of a parameter list.
///
/// Either a named parameter or a positional one.
#[derive(Debug, Clone, Hash, Copy, PartialEq, Eq, From)]
pub enum ParamIndex {
    /// A named parameter, like `foo(value=3)`.
    Name(Identifier),
    /// A positional parameter, like `dot(x, y)`.
    Position(usize),
}

impl From<ParamId> for ParamIndex {
    fn from(value: ParamId) -> Self {
        ParamIndex::Position(value.1)
    }
}

impl ParamIndex {
    /// Get the name of the parameter, if it is named, or a fresh symbol
    /// otherwise.
    pub fn into_symbol(&self) -> Symbol {
        match self {
            ParamIndex::Name(name) => Symbol::from_name(*name),
            ParamIndex::Position(_) => Symbol::fresh(),
        }
    }
}

/// Some kind of parameters or arguments, either [`ParamsId`], [`PatArgsId`] or
/// [`ArgsId`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub enum SomeParamsOrArgsId {
    Params(ParamsId),
    PatArgs(PatArgsId),
    Args(ArgsId),
}

impl SomeParamsOrArgsId {
    /// Get the length of the inner stored parameters.
    pub fn len(&self) -> usize {
        match self {
            SomeParamsOrArgsId::Params(id) => id.len(),
            SomeParamsOrArgsId::PatArgs(id) => id.len(),
            SomeParamsOrArgsId::Args(id) => id.len(),
        }
    }

    /// Whether the inner stored parameters list is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the English subject noun of the [SomeParamsOrArgsId]
    pub fn as_str(&self) -> &'static str {
        match self {
            SomeParamsOrArgsId::Params(_) => "parameters",
            SomeParamsOrArgsId::PatArgs(_) => "pattern arguments",
            SomeParamsOrArgsId::Args(_) => "arguments",
        }
    }
}

impl From<SomeParamsOrArgsId> for IndexedLocationTarget {
    fn from(target: SomeParamsOrArgsId) -> Self {
        match target {
            SomeParamsOrArgsId::Params(id) => IndexedLocationTarget::Params(id),
            SomeParamsOrArgsId::PatArgs(id) => IndexedLocationTarget::PatArgs(id),
            SomeParamsOrArgsId::Args(id) => IndexedLocationTarget::Args(id),
        }
    }
}

/// All the places a parameter can come from.
#[derive(Debug, Clone, Copy, From)]
pub enum ParamOrigin {
    /// A parameter in a function definition.
    Fn(FnDefId),
    /// A parameter in a function type.
    FnTy(FnTy),
    /// A parameter in a tuple type.
    TupleTy(TupleTy),
    /// A parameter in a constructor.
    Ctor(CtorDefId),
    /// A parameter in a data definition.
    Data(DataDefId),
}

impl From<ParamOrigin> for ScopeKind {
    fn from(value: ParamOrigin) -> Self {
        match value {
            ParamOrigin::Fn(fn_def_id) => ScopeKind::Fn(fn_def_id),
            ParamOrigin::FnTy(fn_ty) => ScopeKind::FnTy(fn_ty),
            ParamOrigin::TupleTy(tuple_ty) => ScopeKind::TupleTy(tuple_ty),
            ParamOrigin::Ctor(ctor_def_id) => ScopeKind::Ctor(ctor_def_id),
            ParamOrigin::Data(data_def_id) => ScopeKind::Data(data_def_id),
        }
    }
}

impl ParamOrigin {
    /// A constant parameter is one that cannot depend on non-constant bindings.
    pub fn is_constant(&self) -> bool {
        match self {
            ParamOrigin::Fn(_) | ParamOrigin::FnTy(_) | ParamOrigin::TupleTy(_) => false,
            ParamOrigin::Ctor(_) | ParamOrigin::Data(_) => true,
        }
    }
}

impl ParamsId {
    pub fn at_index(self, index: ParamIndex) -> Option<ParamId> {
        match index {
            ParamIndex::Name(name) => self
                .iter()
                .find(|param| matches!(param.borrow().name.borrow().name, Some(n) if n == name)),
            ParamIndex::Position(pos) => self.at(pos),
        }
    }

    pub fn at_valid_index(self, index: ParamIndex) -> ParamId {
        self.at_index(index).unwrap_or_else(|| {
            panic!("Parameter with name `{}` does not exist in `{}`", index, self)
        })
    }
}

impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {}{}",
            self.name,
            self.ty,
            if let Some(default) = self.default {
                format!(" = {}", default)
            } else {
                "".to_string()
            }
        )
    }
}

impl fmt::Display for ParamId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl fmt::Display for ParamsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, param) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", param)?;
        }
        Ok(())
    }
}

impl fmt::Display for ParamIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParamIndex::Name(name) => write!(f, "{name}"),
            ParamIndex::Position(pos) => write!(f, "{pos}"),
        }
    }
}

impl fmt::Display for SomeParamsOrArgsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SomeParamsOrArgsId::Params(id) => write!(f, "{}", id),
            SomeParamsOrArgsId::PatArgs(id) => write!(f, "{}", id),
            SomeParamsOrArgsId::Args(id) => write!(f, "{}", id),
        }
    }
}
