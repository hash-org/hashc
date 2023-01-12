// @@Docs

use hash_source::identifier::Identifier;
use hash_utils::store::{CloneStore, PartialStore, SequenceStore, SequenceStoreKey, Store};

use crate::new::{
    args::ArgsId,
    defs::{DefParamGroup, DefParamsId},
    environment::env::{AccessToEnv, Env},
    fns::{
        FnBody::{self},
        FnDef, FnTy,
    },
    intrinsics::{Intrinsic, IntrinsicId},
    params::{DefParamIndex, Param, ParamIndex, ParamsId},
    symbols::{Symbol, SymbolData},
    terms::{Term, TermId},
};

/// Assert that the given term is of the given variant, and return it.
#[macro_export]
macro_rules! term_as_variant {
    ($self:expr, value $term:expr, $variant:ident) => {{
        let term = $term;
        if let $crate::new::terms::Term::$variant(term) = term {
            term
        } else {
            panic!("Expected term to be a {}", stringify!($variant))
        }
    }};
}

/// Assert that the given type is of the given variant, and return it.
#[macro_export]
macro_rules! ty_as_variant {
    ($self:expr, value $ty:expr, $variant:ident) => {{
        let ty = $ty;
        if let hash_types::new::tys::Ty::$variant(ty) = ty {
            ty
        } else {
            panic!("Expected type to be a {}", stringify!($variant))
        }
    }};
}

pub trait CommonUtils: AccessToEnv {
    /// Check whether the given term is a void term (i.e. empty tuple).
    fn term_is_void(&self, term_id: TermId) -> bool {
        matches! {
          self.stores().term().get(term_id),
          Term::Tuple(tuple_term) if tuple_term.data.is_empty()
        }
    }

    /// Get the parameter of the given parameters ID and index which is
    /// either symbolic or positional.
    ///
    /// This will panic if the index does not exist.
    fn get_param_by_index(&self, params_id: ParamsId, index: ParamIndex) -> Param {
        match index {
            ParamIndex::Name(name) => self.stores().params().map_fast(params_id, |params| {
                params
                    .iter()
                    .find_map(|x| {
                        if self.stores().symbol().get(x.name).name? == name {
                            Some(*x)
                        } else {
                            None
                        }
                    })
                    .unwrap_or_else(|| {
                        panic!(
                            "Parameter with name `{}` does not exist in `{}`",
                            name,
                            self.env().with(params_id)
                        )
                    })
            }),
            ParamIndex::Position(i) => {
                self.stores().params().map_fast(params_id, |params| params[i])
            }
        }
    }

    /// Get the parameter group of the given definition parameters ID and
    /// positional index.
    ///
    /// This will panic if the index does not exist.
    fn get_param_group_by_index(&self, def_params_id: DefParamsId, index: usize) -> DefParamGroup {
        self.stores().def_params().map_fast(def_params_id, |def_params| def_params[index])
    }

    /// Get the parameter of the given definition parameters ID and
    /// definition parameter index.
    ///
    /// This will panic if the index does not exist.
    fn get_def_param_by_index(&self, def_params_id: DefParamsId, index: DefParamIndex) -> Param {
        let params = self.get_param_group_by_index(def_params_id, index.group_index).params;
        self.get_param_by_index(params, index.param_index)
    }

    /// Create a new symbol with the given name.
    fn new_symbol(&self, name: impl Into<Identifier>) -> Symbol {
        self.stores().symbol().create_with(|symbol| SymbolData { name: Some(name.into()), symbol })
    }

    /// Create an intrinsic function.
    fn make_intrinsic(
        &self,
        name: impl Into<Identifier>,
        ty: FnTy,
        implementation: fn(&Env, ArgsId) -> TermId,
    ) -> IntrinsicId {
        let intrinsic_id = IntrinsicId(self.new_symbol(name));
        let _fn_def_id = self.stores().fn_def().create_with(|fn_def_id| {
            self.stores().intrinsic().insert(
                intrinsic_id,
                Intrinsic { name: intrinsic_id.0, fn_def: fn_def_id, call: implementation },
            );
            FnDef { id: fn_def_id, name: intrinsic_id.0, ty, body: FnBody::Intrinsic(intrinsic_id) }
        });
        intrinsic_id
    }

    /// Create a new empty parameter list.
    fn new_empty_params(&self) -> ParamsId {
        self.stores().params().create_from_slice(&[])
    }
}

impl<T: AccessToEnv> CommonUtils for T {}
