//! This module contains code that can bootstrap the typechecker, by creating
//! and injecting primitive definitions into the context.
use std::{cell::Cell, iter::once};

use derive_more::Constructor;
use hash_types::new::{
    data::{DataDefId, ListCtorInfo, NumericCtorInfo, PrimitiveCtorInfo},
    defs::DefParamGroupData,
    environment::env::AccessToEnv,
    mods::{ModDefData, ModDefId, ModKind, ModMemberData, ModMemberValue},
    params::ParamData,
};
use hash_utils::store::Store;

use super::{common::CommonOps, AccessToOps};
use crate::{
    impl_access_to_tc_env,
    new::environment::tc_env::{AccessToTcEnv, TcEnv},
};

#[derive(Constructor)]
pub struct BootstrapOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

macro_rules! defined_primitives {
    ($($name:ident: $type:ty),* $(,)?) => {
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

        impl<'tc> BootstrapOps<'tc> {
            /// Create a list of [`ModMemberData`] that corresponds to the defined primitives.
            ///
            /// This can be used to make a module and enter its scope.
            pub fn make_primitive_mod_members(&self, primitives: &DefinedPrimitives) -> Vec<ModMemberData> {
                vec![
                    $(
                        ModMemberData {
                            name: self.stores().data_def().map_fast(primitives.$name, |def| def.name),
                            value: ModMemberValue::Data(primitives.$name)
                        },
                    )*
                ]
            }
        }
    };

}

// All the primitive types:
defined_primitives! {
    never: DataDefId,
    bool: DataDefId,
    u8: DataDefId,
    u16: DataDefId,
    u32: DataDefId,
    u64: DataDefId,
    i8: DataDefId,
    i16: DataDefId,
    i32: DataDefId,
    i64: DataDefId,
    usize: DataDefId,
    isize: DataDefId,
    f32: DataDefId,
    f64: DataDefId,
    str: DataDefId,
    char: DataDefId,
    option: DataDefId,
    result: DataDefId,
    list: DataDefId,
}

pub type DefinedPrimitivesOrUnset = Cell<Option<DefinedPrimitives>>;

impl_access_to_tc_env!(BootstrapOps<'tc>);

impl<'tc> BootstrapOps<'tc> {
    /// Bootstrap the typechecker, by creating a module of primitive
    /// definitions and giving them to the provided closure.
    pub fn bootstrap<T>(&self, f: impl FnOnce(ModDefId) -> T) -> T {
        let primitives = self.make_primitives();
        let primitive_mod = self.make_primitive_mod(&primitives);
        self.primitives_or_unset().set(Some(primitives));
        let result = f(primitive_mod);
        self.primitives_or_unset().take();
        result
    }

    /// From the given [`DefinedPrimitives`], create a module that contains
    /// them as members.
    pub fn make_primitive_mod(&self, primitives: &DefinedPrimitives) -> ModDefId {
        self.mod_ops().create_mod_def(ModDefData {
            name: self.new_symbol("Primitives"),
            kind: ModKind::Transparent,
            members: self.mod_ops().create_mod_members(self.make_primitive_mod_members(primitives)),
        })
    }

    /// Make the primitive definitions.
    pub fn make_primitives(&self) -> DefinedPrimitives {
        // Helper function to create a numeric primitive.
        let numeric = |name, bits, signed, float| {
            self.data_ops().create_primitive_data_def(
                self.new_symbol(name),
                PrimitiveCtorInfo::Numeric(NumericCtorInfo {
                    bits,
                    is_signed: signed,
                    is_float: float,
                }),
            )
        };

        DefinedPrimitives {
            // Never
            never: self.data_ops().new_empty_data_def(
                self.new_symbol("never"),
                self.param_ops().new_empty_def_params(),
            ),

            // bool
            bool: self.data_ops().create_enum_def(
                self.new_symbol("bool"),
                self.new_empty_def_params(),
                |_| {
                    vec![
                        (self.new_symbol("true"), self.new_empty_params()),
                        (self.new_symbol("false"), self.new_empty_params()),
                    ]
                },
            ),

            // numerics
            i8: numeric("i8", 8, true, false),
            i16: numeric("i16", 16, true, false),
            i32: numeric("i32", 32, true, false),
            i64: numeric("i64", 64, true, false),
            isize: numeric("isize", 64, true, false),
            u8: numeric("u8", 8, false, false),
            u16: numeric("u16", 16, false, false),
            u32: numeric("u32", 32, false, false),
            u64: numeric("u64", 64, false, false),
            usize: numeric("usize", 64, false, false),
            f32: numeric("f32", 32, false, true),
            f64: numeric("f64", 64, false, true),

            // str and char
            str: self
                .data_ops()
                .create_primitive_data_def(self.new_symbol("str"), PrimitiveCtorInfo::Str),
            char: self
                .data_ops()
                .create_primitive_data_def(self.new_symbol("char"), PrimitiveCtorInfo::Char),

            // list
            list: {
                let list_sym = self.new_symbol("List");
                let t_sym = self.new_symbol("T");
                let params = self.param_ops().create_params(once(ParamData {
                    name: t_sym,
                    ty: self.new_small_universe_ty(),
                    default_value: None,
                }));
                let def_params = self
                    .param_ops()
                    .create_def_params(once(DefParamGroupData { implicit: true, params }));
                self.data_ops().create_primitive_data_def_with_params(list_sym, def_params, |_| {
                    PrimitiveCtorInfo::List(ListCtorInfo { element_ty: self.new_var_ty(t_sym) })
                })
            },

            // option
            option: {
                let option_sym = self.new_symbol("Option");
                let none_sym = self.new_symbol("None");
                let some_sym = self.new_symbol("Some");
                let t_sym = self.new_symbol("T");
                let params = self.param_ops().create_params(once(ParamData {
                    name: t_sym,
                    ty: self.new_small_universe_ty(),
                    default_value: None,
                }));
                let def_params = self
                    .param_ops()
                    .create_def_params(once(DefParamGroupData { implicit: true, params }));
                let some_params = self.param_ops().create_params(once(ParamData {
                    name: self.new_symbol("value"),
                    ty: self.new_var_ty(t_sym),
                    default_value: None,
                }));
                self.data_ops().create_enum_def(option_sym, def_params, |_| {
                    vec![(none_sym, self.new_empty_params()), (some_sym, some_params)]
                })
            },

            // result
            result: {
                let result_sym = self.new_symbol("Result");
                let ok_sym = self.new_symbol("Ok");
                let err_sym = self.new_symbol("Err");
                let t_sym = self.new_symbol("T");
                let e_sym = self.new_symbol("E");
                let params = self.param_ops().create_params(
                    [
                        ParamData {
                            name: t_sym,
                            ty: self.new_small_universe_ty(),
                            default_value: None,
                        },
                        ParamData {
                            name: e_sym,
                            ty: self.new_small_universe_ty(),
                            default_value: None,
                        },
                    ]
                    .into_iter(),
                );
                let def_params = self
                    .param_ops()
                    .create_def_params(once(DefParamGroupData { implicit: true, params }));
                let ok_params = self.param_ops().create_params(once(ParamData {
                    name: self.new_symbol("value"),
                    ty: self.new_var_ty(t_sym),
                    default_value: None,
                }));
                let err_params = self.param_ops().create_params(once(ParamData {
                    name: self.new_symbol("error"),
                    ty: self.new_var_ty(e_sym),
                    default_value: None,
                }));
                self.data_ops().create_enum_def(result_sym, def_params, |_| {
                    vec![(ok_sym, ok_params), (err_sym, err_params)]
                })
            },
        }
    }
}
