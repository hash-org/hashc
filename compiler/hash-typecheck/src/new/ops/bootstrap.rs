use std::iter::once;

use derive_more::Constructor;
use hash_types::new::{
    data::{DataDefId, ListCtorInfo, NumericCtorInfo, PrimitiveCtorInfo},
    defs::DefParamGroupData,
    environment::{context::ScopeKind, env::AccessToEnv},
    mods::{ModDefData, ModDefId, ModKind, ModMemberData, ModMemberValue},
    params::ParamData,
};
use hash_utils::store::Store;

use super::{common::CommonOps, AccessToOps};
use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

#[derive(Constructor)]
pub struct BootstrapOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

macro_rules! defined_primitives {
    ($($name:ident: $type:ty),* $(,)?) => {
        pub struct DefinedPrimitives {
            $(pub $name: DataDefId),*
        }

        impl<'tc> BootstrapOps<'tc> {
            pub fn make_primitive_mod_members(&self) -> Vec<ModMemberData> {
                let primitives = self.make_primitives();
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
    f32: DataDefId,
    f64: DataDefId,
    str: DataDefId,
    char: DataDefId,
    option: DataDefId,
    list: DataDefId,
}

impl_access_to_tc_env!(BootstrapOps<'tc>);

impl<'tc> BootstrapOps<'tc> {
    pub fn bootstrap(&self) {
        self.make_primitives();
    }

    pub fn make_and_enter_primitive_mod(&self) {
        self.context_ops().add_scope(ScopeKind::Mod(self.make_primitive_mod()));
    }

    pub fn make_primitive_mod(&self) -> ModDefId {
        self.mod_ops().create_mod_def(ModDefData {
            name: self.new_symbol("Primitives"),
            params: self.new_empty_def_params(),
            kind: ModKind::Transparent,
            members: self.mod_ops().create_mod_members(self.make_primitive_mod_members()),
            self_ty_name: None,
        })
    }

    pub fn make_primitives(&self) -> DefinedPrimitives {
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
                |_| vec![(self.new_symbol("true"), vec![]), (self.new_symbol("false"), vec![])],
            ),

            // numerics
            i8: numeric("i8", 8, true, false),
            i16: numeric("i16", 16, true, false),
            i32: numeric("i32", 32, true, false),
            i64: numeric("i64", 64, true, false),
            u8: numeric("u8", 8, false, false),
            u16: numeric("u16", 16, false, false),
            u32: numeric("u32", 32, false, false),
            u64: numeric("u64", 64, false, false),
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
                self.data_ops().create_primitive_data_def_with_params(
                    list_sym,
                    self.param_ops().create_def_params(once(DefParamGroupData {
                        implicit: true,
                        params: self.param_ops().create_params(once(ParamData {
                            name: t_sym,
                            ty: self.new_small_universe_ty(),
                            default_value: None,
                        })),
                    })),
                    |id| {
                        PrimitiveCtorInfo::List(ListCtorInfo {
                            element_ty: self.new_var_in_data_params(t_sym, id),
                        })
                    },
                )
            },

            // option
            option: {
                let option_sym = self.new_symbol("Option");
                let none_sym = self.new_symbol("None");
                let some_sym = self.new_symbol("Some");
                let t_sym = self.new_symbol("T");
                self.data_ops().create_enum_def(
                    option_sym,
                    self.param_ops().create_def_params(once(DefParamGroupData {
                        implicit: true,
                        params: self.param_ops().create_params(once(ParamData {
                            name: t_sym,
                            ty: self.new_small_universe_ty(),
                            default_value: None,
                        })),
                    })),
                    |id| {
                        vec![
                            (none_sym, vec![]),
                            (
                                some_sym,
                                vec![ParamData {
                                    name: self.new_symbol("value"),
                                    ty: self.new_var_in_data_params(t_sym, id),
                                    default_value: None,
                                }],
                            ),
                        ]
                    },
                )
            },
        }
    }
}
