//! Definition and lookup of primitive types.
use std::iter::once;

use hash_storage::store::{statics::SequenceStoreValue, Store};
use hash_tir::{
    data::{
        ArrayCtorInfo, DataDef, DataDefId, NumericCtorBits, NumericCtorInfo, PrimitiveCtorInfo,
    },
    environment::env::{AccessToEnv, Env},
    mods::{ModMemberData, ModMemberValue},
    params::{Param, ParamData},
    symbols::sym,
    tys::Ty,
    utils::{common::CommonUtils, AccessToUtils},
};

macro_rules! defined_primitives {
    ($($name:ident),* $(,)?) => {
        #[derive(Debug, Copy, Clone)]
        pub struct DefinedPrimitives {
            $($name: DataDefId),*
        }

        impl DefinedPrimitives {
            $(
                pub fn $name(&self) -> DataDefId {
                    self.$name
                }
            )*
        }

        impl DefinedPrimitives {
            /// Create a list of [`ModMemberData`] that corresponds to the defined primitives.
            ///
            /// This can be used to make a module and enter its scope.
            pub fn as_mod_members(&self, env: &Env) -> Vec<ModMemberData> {
                vec![
                    $(
                        ModMemberData {
                            name: env.stores().data_def().map_fast(self.$name, |def| def.name),
                            value: ModMemberValue::Data(self.$name)
                        },
                    )*
                ]
            }
        }
    };

}

// All the primitive types:
defined_primitives! {
    never,
    bool,
    u8,
    u16,
    u32,
    u64,
    u128,
    ubig,
    usize,
    i8,
    i16,
    i32,
    i64,
    i128,
    ibig,
    isize,
    f32,
    f64,
    str,
    char,
    option,
    result,
    list,
    array,
    equal,
}

impl DefinedPrimitives {
    /// Create the primitive types using the given environment.
    pub fn create<T: AccessToEnv>(env: &T) -> Self {
        // Helper function to create a numeric primitive.
        let numeric = |name, bits, signed, float| {
            DataDef::primitive(
                sym(name),
                PrimitiveCtorInfo::Numeric(NumericCtorInfo {
                    bits: if bits == 0 {
                        NumericCtorBits::Unbounded
                    } else {
                        NumericCtorBits::Bounded(bits)
                    },
                    is_signed: signed,
                    is_float: float,
                }),
            )
        };

        let usize = numeric("usize", 64, false, false);

        DefinedPrimitives {
            // Never
            never: DataDef::empty(sym("never"), Param::empty_seq()),

            // bool
            bool: DataDef::enum_def(sym("bool"), Param::empty_seq(), |_| {
                vec![(sym("true"), Param::empty_seq()), (sym("false"), Param::empty_seq())]
            }),

            // numerics
            i8: numeric("i8", 8, true, false),
            i16: numeric("i16", 16, true, false),
            i32: numeric("i32", 32, true, false),
            i64: numeric("i64", 64, true, false),
            i128: numeric("i128", 128, true, false),
            isize: numeric("isize", 64, true, false),
            ibig: numeric("ibig", 0, true, false),

            u8: numeric("u8", 8, false, false),
            u16: numeric("u16", 16, false, false),
            u32: numeric("u32", 32, false, false),
            u64: numeric("u64", 64, false, false),
            u128: numeric("u128", 128, false, false),
            ubig: numeric("ubig", 0, false, false),
            usize,

            f32: numeric("f32", 32, false, true),
            f64: numeric("f64", 64, false, true),

            // str and char
            str: DataDef::primitive(sym("str"), PrimitiveCtorInfo::Str),
            char: DataDef::primitive(sym("char"), PrimitiveCtorInfo::Char),

            // list
            list: {
                let list_sym = sym("List");
                let t_sym = sym("T");
                let params = env.param_utils().create_params(once(ParamData {
                    name: t_sym,
                    ty: Ty::flexible_universe(),
                    default: None,
                }));
                DataDef::primitive_with_params(list_sym, params, |_| {
                    PrimitiveCtorInfo::Array(ArrayCtorInfo {
                        element_ty: Ty::var(t_sym),
                        length: None,
                    })
                })
            },
            array: {
                let list_sym = sym("Array");
                let t_sym = sym("T");
                let n_sym = sym("n");
                let params = env.param_utils().create_params(
                    [
                        ParamData { name: t_sym, ty: Ty::flexible_universe(), default: None },
                        ParamData { name: n_sym, ty: Ty::data(usize), default: None },
                    ]
                    .into_iter(),
                );
                DataDef::primitive_with_params(list_sym, params, |_| {
                    PrimitiveCtorInfo::Array(ArrayCtorInfo {
                        element_ty: Ty::var(t_sym),
                        length: Some(env.new_term(n_sym)),
                    })
                })
            },

            // option
            option: {
                let option_sym = sym("Option");
                let none_sym = sym("None");
                let some_sym = sym("Some");
                let t_sym = sym("T");
                let params = env.param_utils().create_params(once(ParamData {
                    name: t_sym,
                    ty: Ty::flexible_universe(),
                    default: None,
                }));
                let some_params = env.param_utils().create_params(once(ParamData {
                    name: sym("value"),
                    ty: Ty::var(t_sym),
                    default: None,
                }));
                DataDef::enum_def(option_sym, params, |_| {
                    vec![(none_sym, Param::empty_seq()), (some_sym, some_params)]
                })
            },

            // result
            result: {
                let result_sym = sym("Result");
                let ok_sym = sym("Ok");
                let err_sym = sym("Err");
                let t_sym = sym("T");
                let e_sym = sym("E");
                let params = env.param_utils().create_params(
                    [
                        ParamData { name: t_sym, ty: Ty::flexible_universe(), default: None },
                        ParamData { name: e_sym, ty: Ty::flexible_universe(), default: None },
                    ]
                    .into_iter(),
                );
                let ok_params = env.param_utils().create_params(once(ParamData {
                    name: sym("value"),
                    ty: Ty::var(t_sym),
                    default: None,
                }));
                let err_params = env.param_utils().create_params(once(ParamData {
                    name: sym("error"),
                    ty: Ty::var(e_sym),
                    default: None,
                }));
                DataDef::enum_def(result_sym, params, |_| {
                    vec![(ok_sym, ok_params), (err_sym, err_params)]
                })
            },
            equal: {
                let eq_sym = sym("Equal");
                let refl_sym = sym("Refl");

                let t_sym = sym("T");
                let a_sym = sym("a");
                let b_sym = sym("b");

                let x_sym = sym("x");

                let params = env.param_utils().create_params(
                    [
                        ParamData { name: t_sym, ty: Ty::flexible_universe(), default: None },
                        ParamData { name: a_sym, ty: Ty::var(t_sym), default: None },
                        ParamData { name: b_sym, ty: Ty::var(t_sym), default: None },
                    ]
                    .into_iter(),
                );
                let refl_params = env.param_utils().create_params(once(ParamData {
                    name: x_sym,
                    ty: Ty::var(t_sym),
                    default: None,
                }));

                let refl_result_args = env.param_utils().create_positional_args([
                    env.new_term(t_sym),
                    env.new_term(x_sym),
                    env.new_term(x_sym),
                ]);

                DataDef::indexed_enum_def(eq_sym, params, |_| {
                    vec![(refl_sym, refl_params, Some(refl_result_args))]
                })
            },
        }
    }
}

/// Trait to be able to access the defined primitives.
///
/// More traits can be defined on top of this one.
pub trait AccessToPrimitives: AccessToEnv {
    fn primitives(&self) -> &DefinedPrimitives;
}
