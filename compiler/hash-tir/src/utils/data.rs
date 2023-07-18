//! Data definition-related utilities.
use std::iter::once;

use derive_more::Constructor;
use hash_utils::{
    itertools::Itertools,
    store::{statics::SequenceStoreValue, SequenceStore, SequenceStoreKey, Store},
};

use super::{common::CommonUtils, AccessToUtils};
use crate::{
    args::{ArgData, ArgsId},
    data::{CtorDef, CtorDefData, CtorDefsId, DataDef, DataDefCtors, DataDefId, PrimitiveCtorInfo},
    environment::env::{AccessToEnv, Env},
    impl_access_to_env,
    params::{Param, ParamIndex, ParamsId},
    symbols::Symbol,
    terms::Term,
};

/// Data definition-related operations.
#[derive(Constructor)]
pub struct DataUtils<'tc> {
    env: &'tc Env<'tc>,
}

impl_access_to_env!(DataUtils<'tc>);

impl<'tc> DataUtils<'tc> {
    /// Create an empty data definition.
    pub fn new_empty_data_def(&self, name: Symbol, params: ParamsId) -> DataDefId {
        self.stores().data_def().create_with(|id| DataDef {
            id,
            name,
            params,
            ctors: DataDefCtors::Defined(self.stores().ctor_defs().create_from_slice(&[])),
        })
    }

    /// Set the constructors of the given data definition.
    pub fn set_data_def_ctors(&self, data_def: DataDefId, ctors: CtorDefsId) -> CtorDefsId {
        self.stores().data_def().modify_fast(data_def, |data_def| {
            data_def.ctors = DataDefCtors::Defined(ctors);
        });
        ctors
    }

    /// Get the single constructor of the given data definition, if it is indeed
    /// a single constructor.
    pub fn get_single_ctor_of_data_def(&self, data_def: DataDefId) -> Option<CtorDef> {
        match self.stores().data_def().map_fast(data_def, |def| def.ctors) {
            DataDefCtors::Defined(ctors) => {
                if ctors.len() == 1 {
                    Some(self.stores().ctor_defs().map_fast(ctors, |ctors| ctors[0]))
                } else {
                    None
                }
            }
            DataDefCtors::Primitive(_) => None,
        }
    }

    /// Create a primitive data definition.
    pub fn create_primitive_data_def(&self, name: Symbol, info: PrimitiveCtorInfo) -> DataDefId {
        self.stores().data_def().create_with(|id| DataDef {
            id,
            name,
            params: Param::empty_seq(),
            ctors: DataDefCtors::Primitive(info),
        })
    }

    /// Create a primitive data definition with parameters.
    ///
    /// These may be referenced in `info`.
    pub fn create_primitive_data_def_with_params(
        &self,
        name: Symbol,
        params: ParamsId,
        info: impl FnOnce(DataDefId) -> PrimitiveCtorInfo,
    ) -> DataDefId {
        self.stores().data_def().create_with(|id| DataDef {
            id,
            name,
            params,
            ctors: DataDefCtors::Primitive(info(id)),
        })
    }

    /// Create data constructors from the given iterator, for the given data
    /// definition.
    pub fn create_data_ctors<I: IntoIterator<Item = CtorDefData>>(
        &self,
        data_def_id: DataDefId,
        data: I,
    ) -> CtorDefsId
    where
        I::IntoIter: ExactSizeIterator,
    {
        self.stores().ctor_defs().create_from_iter_with(data.into_iter().enumerate().map(
            |(index, data)| {
                move |id| CtorDef {
                    id,
                    name: data.name,
                    data_def_id,
                    data_def_ctor_index: index,
                    params: data.params,
                    result_args: data.result_args,
                }
            },
        ))
    }

    /// From the given definition parameters corresponding to the given data
    /// definition, create definition arguments that directly refer to the
    /// parameters from the data definition scope.
    ///
    /// Example:
    /// ```notrust
    /// X := datatype <A: Type, B: Type, C: Type> { foo: () -> X<A, B, C> }
    ///                                                         ^^^^^^^^^ this is what this function creates
    /// ```
    pub fn create_forwarded_data_args_from_params(
        &self,
        _data_def_id: DataDefId,
        params_id: ParamsId,
    ) -> ArgsId {
        self.param_utils().create_args(self.stores().params().map(params_id, |params| {
            // For each parameter, create an argument referring to it
            params
                .iter()
                .enumerate()
                .map(|(i, param)| ArgData {
                    target: ParamIndex::Position(i),
                    value: self.new_term(Term::Var(param.name)),
                })
                .collect_vec()
                .into_iter()
        }))
    }

    /// Create a struct data definition, with some parameters.
    ///
    /// The fields are given as an iterator of `ParamData`s, which are the names
    /// and types of the fields.
    ///
    /// This will create a data definition with a single constructor, which
    /// takes the fields as parameters and returns the data type.
    pub fn create_struct_def(
        &self,
        name: Symbol,
        params: ParamsId,
        fields_params: ParamsId,
    ) -> DataDefId {
        // Create the arguments for the constructor, which are the type
        // parameters given.
        let result_args =
            |data_def_id| self.create_forwarded_data_args_from_params(data_def_id, params);

        // Create the data definition
        self.stores().data_def().create_with(|id| DataDef {
            id,
            name,
            params,
            ctors: DataDefCtors::Defined(self.stores().ctor_defs().create_from_iter_with(once(
                |ctor_id| {
                    CtorDef {
                        id: ctor_id,
                        // Name of the constructor is the same as the data definition, though we
                        // need to create a new symbol for it
                        name: self.duplicate_symbol(name),
                        // The constructor is the only one
                        data_def_ctor_index: 0,
                        data_def_id: id,
                        params: fields_params,
                        result_args: result_args(id),
                    }
                },
            ))),
        })
    }

    /// Create an enum definition, with some parameters, where each variant has
    /// specific result arguments.
    pub fn create_data_def(
        &self,
        name: Symbol,
        params: ParamsId,
        variants: impl Fn(DataDefId) -> Vec<(Symbol, ParamsId, Option<ArgsId>)>,
    ) -> DataDefId {
        // Create the data definition for the enum
        self.stores().data_def().create_with(|id| DataDef {
            id,
            name,
            params,
            ctors: DataDefCtors::Defined(self.stores().ctor_defs().create_from_iter_with(
                variants(id).into_iter().enumerate().map(
                    |(index, (variant_name, fields_params, result_args))| {
                        // Create a constructor for each variant
                        move |ctor_id| CtorDef {
                            id: ctor_id,
                            name: variant_name,
                            data_def_ctor_index: index,
                            data_def_id: id,
                            params: fields_params,
                            result_args: result_args.unwrap_or_else(|| {
                                // Create the arguments for the constructor, which are the type
                                // parameters given.
                                self.create_forwarded_data_args_from_params(id, params)
                            }),
                        }
                    },
                ),
            )),
        })
    }

    /// Create an enum definition, with some parameters.
    ///
    /// The variants are given as an iterator of `(Symbol, Iter<ParamData>)`,
    /// which are the names and fields of the variants.
    ///
    /// This will create a data definition with a constructor for each variant,
    /// which takes the variant fields as parameters and returns the data
    /// type.
    pub fn create_enum_def(
        &self,
        name: Symbol,
        params: ParamsId,
        variants: impl Fn(DataDefId) -> Vec<(Symbol, ParamsId)>,
    ) -> DataDefId {
        self.create_data_def(name, params, |def_id| {
            variants(def_id)
                .into_iter()
                .map(|(variant_name, fields_params)| (variant_name, fields_params, None))
                .collect_vec()
        })
    }
}
