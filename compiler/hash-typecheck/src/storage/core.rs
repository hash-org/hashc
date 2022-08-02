//! Contains all the core type and trait definitions of the language.
//!
//! These are accessed during the AST traversal in order to type certain
//! language primitives (for example `if`-block subjects). This is because a lot
//! of the "primitive" Hash types aren't actually primitives as far as the
//! typechecker is concerned. This includes: integers, floats, characters,
//! strings, lists, maps, references, etc.
//!
//! This accessing is done through [crate::ops::core::CoreDefReader].
use hash_ast::ast::ParamOrigin;

use super::{
    primitives::{Member, ModDefOrigin, ScopeKind, Visibility},
    GlobalStorage,
};
use crate::ops::building::PrimitiveBuilder;

/// Create the core language type and trait definitions in the given
/// [GlobalStorage], and add their symbols to the root scope.
pub fn create_core_defs_in(global_storage: &mut GlobalStorage) {
    // @@Safety: core defs have not been filled in global_storage, don't access
    // global_storage.core_defs()!
    //
    // We use the root scope as the population scope, since these are the core
    // definitions.
    let builder = PrimitiveBuilder::new_with_scope(global_storage, global_storage.root_scope);

    // Primitive integers
    let _i8_ty = builder.create_opaque_struct_def("i8");

    let _i16_ty = builder.create_opaque_struct_def("i16");
    let i32_ty = builder.create_opaque_struct_def("i32");
    let _i64_ty = builder.create_opaque_struct_def("i64");

    let _u8_ty = builder.create_opaque_struct_def("u8");
    let _u16_ty = builder.create_opaque_struct_def("u16");
    let _u32_ty = builder.create_opaque_struct_def("u32");
    let u64_ty = builder.create_opaque_struct_def("u64");

    let _f32_ty = builder.create_opaque_struct_def("f32");
    let _f64_ty = builder.create_opaque_struct_def("f64");

    // Char and bool
    let _char_ty = builder.create_opaque_struct_def("char");
    let bool_ty = builder.create_enum_def(
        Some("bool"),
        [
            builder
                .create_enum_variant("true", builder.create_params([], ParamOrigin::EnumVariant)),
            builder
                .create_enum_variant("false", builder.create_params([], ParamOrigin::EnumVariant)),
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
    let _str_ty = builder.create_opaque_struct_def("str");

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
    let _reference_ty_fn = builder.create_ty_fn_term(
        Some("Ref"),
        builder.create_params([builder.create_param("T", ty_term)], ParamOrigin::TyFn),
        ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
    let _reference_mut_ty_fn = builder.create_ty_fn_term(
        Some("RefMut"),
        builder.create_params([builder.create_param("T", ty_term)], ParamOrigin::TyFn),
        ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
    let _raw_reference_ty_fn = builder.create_ty_fn_term(
        Some("RawRef"),
        builder.create_params([builder.create_param("T", ty_term)], ParamOrigin::TyFn),
        ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
    let _raw_reference_mut_ty_fn = builder.create_ty_fn_term(
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
                Member::uninitialised_constant("Self", Visibility::Public, ty_term),
                Member::uninitialised_constant(
                    "hash",
                    Visibility::Public,
                    builder.create_fn_ty_term(
                        builder.create_params(
                            [builder.create_param("value", builder.create_var_term("Self"))],
                            ParamOrigin::Fn,
                        ),
                        builder.create_nominal_def_term(u64_ty),
                    ),
                ),
            ],
        ),
    );
    let eq_trt = builder.create_trt_def(
        Some("Eq"),
        builder.create_scope(
            ScopeKind::Constant,
            [
                Member::uninitialised_constant("Self", Visibility::Public, ty_term),
                Member::uninitialised_constant(
                    "eq",
                    Visibility::Public,
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
                Member::uninitialised_constant("Self", Visibility::Public, ty_term),
                Member::uninitialised_constant("Index", Visibility::Public, ty_term),
                Member::uninitialised_constant("Output", Visibility::Public, ty_term),
                Member::uninitialised_constant(
                    "index",
                    Visibility::Public,
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
                Member::open_constant(
                    "Self",
                    Visibility::Public,
                    ty_term,
                    builder.create_app_ty_fn_term(
                        builder.create_var_term("List"),
                        builder.create_args(
                            [builder.create_nameless_arg(builder.create_var_term("T"))],
                            ParamOrigin::TyFn,
                        ),
                    ),
                ),
                Member::open_constant(
                    "Index",
                    Visibility::Public,
                    ty_term,
                    // @@Todo: change this to use usize once we have a better way of inferring
                    // numerics.
                    builder.create_nominal_def_term(i32_ty),
                ),
                Member::open_constant(
                    "Output",
                    Visibility::Public,
                    ty_term,
                    builder.create_var_term("T"),
                ),
                Member::open_constant(
                    "index",
                    Visibility::Public,
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
                                    builder.create_param("self", builder.create_var_term("Self")),
                                    builder.create_param("index", builder.create_var_term("Index")),
                                ],
                                ParamOrigin::Fn,
                            ),
                            builder.create_var_term("Output"),
                        ),
                        builder.create_rt_term(builder.create_var_term("Output")),
                    ),
                ),
            ],
        ),
    );
    let _list_ty_fn = builder.create_ty_fn_term(
        Some("List"),
        builder.create_params([builder.create_param("T", ty_term)], ParamOrigin::TyFn),
        ty_term,
        builder.create_merge_term([
            builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
            builder.create_mod_def_term(list_index_impl),
        ]),
    );

    let _set_ty_fn = builder.create_ty_fn_term(
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

    let _map_ty_fn = builder.create_ty_fn_term(
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
}
