//! Definition and lookup of primitive types.
use std::iter::once;

use hash_tir::{
    data::{ArrayCtorInfo, DataDefId, NumericCtorBits, NumericCtorInfo, PrimitiveCtorInfo},
    environment::env::{AccessToEnv, Env},
    mods::{ModMemberData, ModMemberValue},
    params::ParamData,
    utils::{common::CommonUtils, AccessToUtils},
};
use hash_utils::store::Store;

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
    equal,
}

impl DefinedPrimitives {
    /// Create the primitive types using the given environment.
    pub fn create<T: AccessToEnv>(env: &T) -> Self {
        // Helper function to create a numeric primitive.
        let numeric = |name, bits, signed, float| {
            env.data_utils().create_primitive_data_def(
                env.new_symbol(name),
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

        DefinedPrimitives {
            // Never
            never: env
                .data_utils()
                .new_empty_data_def(env.new_symbol("never"), env.param_utils().new_empty_params()),

            // bool
            bool: env.data_utils().create_enum_def(
                env.new_symbol("bool"),
                env.new_empty_params(),
                |_| {
                    vec![
                        (env.new_symbol("true"), env.new_empty_params()),
                        (env.new_symbol("false"), env.new_empty_params()),
                    ]
                },
            ),

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
            usize: numeric("usize", 64, false, false),

            f32: numeric("f32", 32, false, true),
            f64: numeric("f64", 64, false, true),

            // str and char
            str: env
                .data_utils()
                .create_primitive_data_def(env.new_symbol("str"), PrimitiveCtorInfo::Str),
            char: env
                .data_utils()
                .create_primitive_data_def(env.new_symbol("char"), PrimitiveCtorInfo::Char),

            // list
            list: {
                let list_sym = env.new_symbol("List");
                let t_sym = env.new_symbol("T");
                let params = env.param_utils().create_params(once(ParamData {
                    name: t_sym,
                    ty: env.new_small_universe_ty(),
                    default: None,
                }));
                env.data_utils().create_primitive_data_def_with_params(list_sym, params, |_| {
                    PrimitiveCtorInfo::Array(ArrayCtorInfo {
                        element_ty: env.new_var_ty(t_sym),
                        length: 0,
                    })
                })
            },

            // option
            option: {
                let option_sym = env.new_symbol("Option");
                let none_sym = env.new_symbol("None");
                let some_sym = env.new_symbol("Some");
                let t_sym = env.new_symbol("T");
                let params = env.param_utils().create_params(once(ParamData {
                    name: t_sym,
                    ty: env.new_small_universe_ty(),
                    default: None,
                }));
                let some_params = env.param_utils().create_params(once(ParamData {
                    name: env.new_symbol("value"),
                    ty: env.new_var_ty(t_sym),
                    default: None,
                }));
                env.data_utils().create_enum_def(option_sym, params, |_| {
                    vec![(none_sym, env.new_empty_params()), (some_sym, some_params)]
                })
            },

            // result
            result: {
                let result_sym = env.new_symbol("Result");
                let ok_sym = env.new_symbol("Ok");
                let err_sym = env.new_symbol("Err");
                let t_sym = env.new_symbol("T");
                let e_sym = env.new_symbol("E");
                let params = env.param_utils().create_params(
                    [
                        ParamData { name: t_sym, ty: env.new_small_universe_ty(), default: None },
                        ParamData { name: e_sym, ty: env.new_small_universe_ty(), default: None },
                    ]
                    .into_iter(),
                );
                let ok_params = env.param_utils().create_params(once(ParamData {
                    name: env.new_symbol("value"),
                    ty: env.new_var_ty(t_sym),
                    default: None,
                }));
                let err_params = env.param_utils().create_params(once(ParamData {
                    name: env.new_symbol("error"),
                    ty: env.new_var_ty(e_sym),
                    default: None,
                }));
                env.data_utils().create_enum_def(result_sym, params, |_| {
                    vec![(ok_sym, ok_params), (err_sym, err_params)]
                })
            },
            equal: {
                let eq_sym = env.new_symbol("Equal");
                let refl_sym = env.new_symbol("Refl");

                let t_sym = env.new_symbol("T");
                let a_sym = env.new_symbol("a");
                let b_sym = env.new_symbol("b");

                let x_sym = env.new_symbol("x");

                let params = env.param_utils().create_params(
                    [
                        ParamData { name: t_sym, ty: env.new_small_universe_ty(), default: None },
                        ParamData { name: a_sym, ty: env.new_var_ty(t_sym), default: None },
                        ParamData { name: b_sym, ty: env.new_var_ty(t_sym), default: None },
                    ]
                    .into_iter(),
                );
                let refl_params = env.param_utils().create_params(once(ParamData {
                    name: x_sym,
                    ty: env.new_var_ty(t_sym),
                    default: None,
                }));

                let refl_result_args = env.param_utils().create_positional_args(
                    [env.new_term(t_sym), env.new_term(x_sym), env.new_term(x_sym)].into_iter(),
                );

                env.data_utils().create_data_def(eq_sym, params, |_| {
                    vec![(refl_sym, refl_params, refl_result_args)]
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
