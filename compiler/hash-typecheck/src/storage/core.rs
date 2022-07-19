//! Contains all the core type and trait definitions of the language.
//!
//! These are accessed during the AST traversal in order to type certain
//! language primitives (for example `if`-block subjects). This is because a lot
//! of the "primitive" Hash types aren't actually primitives as far as the
//! typechecker is concerned. This includes: integers, floats, characters,
//! strings, lists, maps, references, etc.
use hash_ast::ast::ParamOrigin;

use super::{
    primitives::{ModDefOrigin, NominalDefId, ScopeKind, TermId, TrtDefId, Visibility},
    GlobalStorage,
};
use crate::ops::building::PrimitiveBuilder;

/// Contains all the core type and trait definitions of the language.
#[derive(Debug, Clone)]
pub struct CoreDefs {
    pub str_ty: NominalDefId,
    pub list_ty_fn: TermId,
    pub map_ty_fn: TermId,
    pub set_ty_fn: TermId,
    pub i8_ty: NominalDefId,
    pub i16_ty: NominalDefId,
    pub i32_ty: NominalDefId,
    pub i64_ty: NominalDefId,
    pub u8_ty: NominalDefId,
    pub u16_ty: NominalDefId,
    pub u32_ty: NominalDefId,
    pub u64_ty: NominalDefId,
    pub f32_ty: NominalDefId,
    pub f64_ty: NominalDefId,
    pub char_ty: NominalDefId,
    pub bool_ty: NominalDefId,
    pub any_ty: TermId,
    pub reference_ty_fn: TermId,
    pub reference_mut_ty_fn: TermId,
    pub raw_reference_ty_fn: TermId,
    pub raw_reference_mut_ty_fn: TermId,
    pub hash_trt: TrtDefId,
    pub eq_trt: TrtDefId,
    pub index_trt: TrtDefId,
    pub runtime_instantiable_trt: TrtDefId,
}

impl CoreDefs {
    /// Create the core language type and trait definitions in the given
    /// [GlobalStorage], and add their symbols to the root scope.
    pub fn new(global_storage: &mut GlobalStorage) -> Self {
        // @@Safety: core defs have not been filled in global_storage, don't access
        // global_storage.core_defs()!
        //
        // We use the root scope as the population scope, since these are the core
        // definitions.
        let builder = PrimitiveBuilder::new_with_scope(global_storage, global_storage.root_scope);

        // Primitive integers
        let i8_ty = builder.create_opaque_struct_def("i8");
        let i16_ty = builder.create_opaque_struct_def("i16");
        let i32_ty = builder.create_opaque_struct_def("i32");
        let i64_ty = builder.create_opaque_struct_def("i64");

        let u8_ty = builder.create_opaque_struct_def("u8");
        let u16_ty = builder.create_opaque_struct_def("u16");
        let u32_ty = builder.create_opaque_struct_def("u32");
        let u64_ty = builder.create_opaque_struct_def("u64");

        let f32_ty = builder.create_opaque_struct_def("f32");
        let f64_ty = builder.create_opaque_struct_def("f64");

        // Char and bool
        let char_ty = builder.create_opaque_struct_def("char");
        let bool_ty = builder.create_enum_def(
            Some("bool"),
            [
                builder.create_enum_variant(
                    "true",
                    builder.create_params([], ParamOrigin::EnumVariant),
                ),
                builder.create_enum_variant(
                    "false",
                    builder.create_params([], ParamOrigin::EnumVariant),
                ),
            ],
        );
        let bool_ty_term = builder.create_nominal_def_term(bool_ty);
        builder.add_pub_member_to_scope(
            "true",
            bool_ty_term,
            builder.create_enum_variant_value_term("true", bool_ty),
        );
        builder.add_pub_member_to_scope(
            "false",
            bool_ty_term,
            builder.create_enum_variant_value_term("false", bool_ty),
        );

        // String
        let str_ty = builder.create_opaque_struct_def("str");

        // Any type
        let any_ty = builder.create_any_ty_term();
        builder.add_pub_member_to_scope("AnyType", builder.create_trt_kind_term(), any_ty);

        // Marker trait for types that are runtime instantiable
        // We call this "Type" because that's what people usually mean when they say
        // "type".
        let runtime_instantiable_trt =
            builder.create_trt_def(Some("Type"), builder.create_scope(ScopeKind::Constant, []));

        // Helper for general type bound
        let ty_term = builder.create_trt_term(runtime_instantiable_trt);

        // Never type
        let never_ty = builder.create_never_term();
        builder.add_pub_member_to_scope(
            "never",
            builder.create_trt_term(runtime_instantiable_trt),
            never_ty,
        );

        // Void type
        let void_ty = builder.create_void_ty_term();
        builder.add_pub_member_to_scope(
            "void",
            builder.create_trt_term(runtime_instantiable_trt),
            void_ty,
        );

        // Reference types
        let reference_ty_fn = builder.create_ty_fn_term(
            Some("Ref"),
            builder.create_params([builder.create_param("T", ty_term)], ParamOrigin::TyFn),
            ty_term,
            builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
        );
        let reference_mut_ty_fn = builder.create_ty_fn_term(
            Some("RefMut"),
            builder.create_params([builder.create_param("T", ty_term)], ParamOrigin::TyFn),
            ty_term,
            builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
        );
        let raw_reference_ty_fn = builder.create_ty_fn_term(
            Some("RawRef"),
            builder.create_params([builder.create_param("T", ty_term)], ParamOrigin::TyFn),
            ty_term,
            builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
        );
        let raw_reference_mut_ty_fn = builder.create_ty_fn_term(
            Some("RawRefMut"),
            builder.create_params([builder.create_param("T", ty_term)], ParamOrigin::TyFn),
            ty_term,
            builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
        );

        // @@Incomplete: these traits should take ref self, not self.

        // Hash and Eq traits
        let hash_trt = builder.create_trt_def(
            Some("Hash"),
            builder.create_scope(
                ScopeKind::Constant,
                [
                    builder.create_uninitialised_constant_member(
                        "Self",
                        ty_term,
                        Visibility::Public,
                    ),
                    builder.create_uninitialised_constant_member(
                        "hash",
                        builder.create_fn_ty_term(
                            builder.create_params(
                                [builder.create_param("value", builder.create_var_term("Self"))],
                                ParamOrigin::Fn,
                            ),
                            builder.create_nominal_def_term(u64_ty),
                        ),
                        Visibility::Public,
                    ),
                ],
            ),
        );
        let eq_trt = builder.create_trt_def(
            Some("Eq"),
            builder.create_scope(
                ScopeKind::Constant,
                [
                    builder.create_uninitialised_constant_member(
                        "Self",
                        ty_term,
                        Visibility::Public,
                    ),
                    builder.create_uninitialised_constant_member(
                        "eq",
                        builder.create_fn_ty_term(
                            builder.create_params(
                                [
                                    builder.create_param("a", builder.create_var_term("Self")),
                                    builder.create_param("b", builder.create_var_term("Self")),
                                ],
                                ParamOrigin::Fn,
                            ),
                            builder.create_nominal_def_term(u64_ty),
                        ),
                        Visibility::Public,
                    ),
                ],
            ),
        );

        // Index trait
        let index_trt = builder.create_trt_def(
            Some("Index"),
            builder.create_scope(
                ScopeKind::Constant,
                [
                    builder.create_uninitialised_constant_member(
                        "Self",
                        ty_term,
                        Visibility::Public,
                    ),
                    builder.create_uninitialised_constant_member(
                        "Index",
                        ty_term,
                        Visibility::Public,
                    ),
                    builder.create_uninitialised_constant_member(
                        "Output",
                        ty_term,
                        Visibility::Public,
                    ),
                    builder.create_uninitialised_constant_member(
                        "index",
                        builder.create_fn_ty_term(
                            builder.create_params(
                                [
                                    builder.create_param("self", builder.create_var_term("Self")),
                                    builder.create_param("index", builder.create_var_term("Index")),
                                ],
                                ParamOrigin::Fn,
                            ),
                            builder.create_var_term("Output"),
                        ),
                        Visibility::Public,
                    ),
                ],
            ),
        );

        // Collection types
        let index_trt_term = builder.create_trt_term(index_trt);
        let list_index_impl = builder.create_nameless_mod_def(
            ModDefOrigin::TrtImpl(index_trt_term),
            builder.create_scope(
                ScopeKind::Constant,
                [
                    builder.create_constant_member(
                        "Self",
                        ty_term,
                        builder.create_app_ty_fn_term(
                            builder.create_var_term("List"),
                            builder.create_args(
                                [builder.create_nameless_arg(builder.create_var_term("T"))],
                                ParamOrigin::TyFn,
                            ),
                        ),
                        Visibility::Public,
                    ),
                    builder.create_constant_member(
                        "Index",
                        ty_term,
                        // @@Todo: change this to use usize once we have a better way of inferring
                        // numerics.
                        builder.create_nominal_def_term(i32_ty),
                        Visibility::Public,
                    ),
                    builder.create_constant_member(
                        "Output",
                        ty_term,
                        builder.create_var_term("T"),
                        Visibility::Public,
                    ),
                    builder.create_constant_member(
                        "index",
                        builder.create_fn_ty_term(
                            builder.create_params(
                                [
                                    builder.create_param("self", builder.create_var_term("Self")),
                                    builder.create_param("index", builder.create_var_term("Index")),
                                ],
                                ParamOrigin::Fn,
                            ),
                            builder.create_var_term("Output"),
                        ),
                        builder.create_fn_lit_term(
                            builder.create_fn_ty_term(
                                builder.create_params(
                                    [
                                        builder
                                            .create_param("self", builder.create_var_term("Self")),
                                        builder.create_param(
                                            "index",
                                            builder.create_var_term("Index"),
                                        ),
                                    ],
                                    ParamOrigin::Fn,
                                ),
                                builder.create_var_term("Output"),
                            ),
                            builder.create_rt_term(builder.create_var_term("Output")),
                        ),
                        Visibility::Public,
                    ),
                ],
            ),
        );
        let list_ty_fn = builder.create_ty_fn_term(
            Some("List"),
            builder.create_params([builder.create_param("T", ty_term)], ParamOrigin::TyFn),
            ty_term,
            builder.create_merge_term([
                builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
                builder.create_mod_def_term(list_index_impl),
            ]),
        );

        let set_ty_fn = builder.create_ty_fn_term(
            Some("Set"),
            builder.create_params(
                [builder.create_param(
                    "T",
                    builder.create_merge_term([
                        builder.create_trt_term(hash_trt),
                        builder.create_trt_term(eq_trt),
                    ]),
                )],
                ParamOrigin::TyFn,
            ),
            ty_term,
            builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
        );

        let map_ty_fn = builder.create_ty_fn_term(
            Some("Map"),
            builder.create_params(
                [
                    builder.create_param(
                        "K",
                        builder.create_merge_term([
                            builder.create_trt_term(hash_trt),
                            builder.create_trt_term(eq_trt),
                        ]),
                    ),
                    builder.create_param("V", ty_term),
                ],
                ParamOrigin::TyFn,
            ),
            ty_term,
            builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
        );

        Self {
            str_ty,
            list_ty_fn,
            map_ty_fn,
            set_ty_fn,
            i8_ty,
            i16_ty,
            i32_ty,
            i64_ty,
            u8_ty,
            u16_ty,
            u32_ty,
            u64_ty,
            f32_ty,
            f64_ty,
            char_ty,
            bool_ty,
            any_ty,
            reference_ty_fn,
            raw_reference_mut_ty_fn,
            raw_reference_ty_fn,
            reference_mut_ty_fn,
            hash_trt,
            eq_trt,
            index_trt,
            runtime_instantiable_trt,
        }
    }
}
