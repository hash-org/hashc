//! Contains all the core type and trait definitions of the language.
//!
//! These are accessed during the AST traversal in order to type certain
//! language primitives (for example `if`-block subjects). This is because a lot
//! of the CORE_IDENTIFIERS.primitive Hash types aren't actually primitives as
//! far as the typechecker is concerned. This includes: integers, floats,
//! characters, strings, lists, maps, references, etc.
//!
//! This accessing is done through [crate::ops::core::CoreDefReader].
use hash_ast::ast::ParamOrigin;
use hash_source::identifier::CORE_IDENTIFIERS;

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
    let _i8_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.i8);

    let _i16_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.i16);
    let i32_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.i32);
    let _i64_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.i64);

    let _u8_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.u8);
    let _u16_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.u16);
    let _u32_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.u32);
    let u64_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.u64);

    let _f32_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.f32);
    let _f64_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.f64);

    // Char and bool
    let _char_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.char);
    let bool_ty = builder.create_enum_def(
        Some(CORE_IDENTIFIERS.bool),
        [
            builder.create_enum_variant(
                CORE_IDENTIFIERS.r#true,
                builder.create_params([], ParamOrigin::EnumVariant),
            ),
            builder.create_enum_variant(
                CORE_IDENTIFIERS.r#false,
                builder.create_params([], ParamOrigin::EnumVariant),
            ),
        ],
    );
    let bool_ty_term = builder.create_nominal_def_term(bool_ty);
    builder.add_pub_member_to_scope(
        CORE_IDENTIFIERS.r#true,
        bool_ty_term,
        builder.create_enum_variant_value_term(CORE_IDENTIFIERS.r#true, bool_ty),
    );
    builder.add_pub_member_to_scope(
        CORE_IDENTIFIERS.r#false,
        bool_ty_term,
        builder.create_enum_variant_value_term(CORE_IDENTIFIERS.r#false, bool_ty),
    );

    // String
    let _str_ty = builder.create_opaque_struct_def(CORE_IDENTIFIERS.str);

    // Any type
    let any_ty = builder.create_any_ty_term();
    builder.add_pub_member_to_scope(
        CORE_IDENTIFIERS.AnyType,
        builder.create_trt_kind_term(),
        any_ty,
    );

    // Marker trait for types that are runtime instantiable
    // We call this CORE_IDENTIFIERS.Type because that's what people usually mean
    // when they say CORE_IDENTIFIERS.type.
    let runtime_instantiable_trt = builder
        .create_trt_def(Some(CORE_IDENTIFIERS.Type), builder.create_scope(ScopeKind::Constant, []));

    // Helper for general type bound
    let ty_term = builder.create_trt_term(runtime_instantiable_trt);

    // Never type
    let never_ty = builder.create_never_term();
    builder.add_pub_member_to_scope(
        CORE_IDENTIFIERS.never,
        builder.create_trt_term(runtime_instantiable_trt),
        never_ty,
    );

    // Void type
    let void_ty = builder.create_void_ty_term();
    builder.add_pub_member_to_scope(
        CORE_IDENTIFIERS.void,
        builder.create_trt_term(runtime_instantiable_trt),
        void_ty,
    );

    // Reference types
    let _reference_ty_fn = builder.create_ty_fn_term(
        Some(CORE_IDENTIFIERS.Ref),
        builder
            .create_params([builder.create_param(CORE_IDENTIFIERS.T, ty_term)], ParamOrigin::TyFn),
        ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
    let _reference_mut_ty_fn = builder.create_ty_fn_term(
        Some(CORE_IDENTIFIERS.RefMut),
        builder
            .create_params([builder.create_param(CORE_IDENTIFIERS.T, ty_term)], ParamOrigin::TyFn),
        ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
    let _raw_reference_ty_fn = builder.create_ty_fn_term(
        Some(CORE_IDENTIFIERS.RawRef),
        builder
            .create_params([builder.create_param(CORE_IDENTIFIERS.T, ty_term)], ParamOrigin::TyFn),
        ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
    let _raw_reference_mut_ty_fn = builder.create_ty_fn_term(
        Some(CORE_IDENTIFIERS.RawRefMut),
        builder
            .create_params([builder.create_param(CORE_IDENTIFIERS.T, ty_term)], ParamOrigin::TyFn),
        ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );

    // @@Incomplete: these traits should take ref self, not self.

    // Hash and Eq traits
    let hash_trt = builder.create_trt_def(
        Some(CORE_IDENTIFIERS.Hash),
        builder.create_scope(
            ScopeKind::Constant,
            [
                Member::uninitialised_constant(
                    CORE_IDENTIFIERS.Self_i,
                    Visibility::Public,
                    ty_term,
                ),
                Member::uninitialised_constant(
                    CORE_IDENTIFIERS.hash,
                    Visibility::Public,
                    builder.create_fn_ty_term(
                        builder.create_params(
                            [builder.create_param(
                                CORE_IDENTIFIERS.value,
                                builder.create_var_term(CORE_IDENTIFIERS.Self_i),
                            )],
                            ParamOrigin::Fn,
                        ),
                        builder.create_nominal_def_term(u64_ty),
                    ),
                ),
            ],
        ),
    );
    let eq_trt = builder.create_trt_def(
        Some(CORE_IDENTIFIERS.Eq),
        builder.create_scope(
            ScopeKind::Constant,
            [
                Member::uninitialised_constant(
                    CORE_IDENTIFIERS.Self_i,
                    Visibility::Public,
                    ty_term,
                ),
                Member::uninitialised_constant(
                    CORE_IDENTIFIERS.eq,
                    Visibility::Public,
                    builder.create_fn_ty_term(
                        builder.create_params(
                            [
                                builder.create_param(
                                    CORE_IDENTIFIERS.a,
                                    builder.create_var_term(CORE_IDENTIFIERS.Self_i),
                                ),
                                builder.create_param(
                                    CORE_IDENTIFIERS.b,
                                    builder.create_var_term(CORE_IDENTIFIERS.Self_i),
                                ),
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
        Some(CORE_IDENTIFIERS.Index),
        builder.create_scope(
            ScopeKind::Constant,
            [
                Member::uninitialised_constant(
                    CORE_IDENTIFIERS.Self_i,
                    Visibility::Public,
                    ty_term,
                ),
                Member::uninitialised_constant(CORE_IDENTIFIERS.Index, Visibility::Public, ty_term),
                Member::uninitialised_constant(
                    CORE_IDENTIFIERS.Output,
                    Visibility::Public,
                    ty_term,
                ),
                Member::uninitialised_constant(
                    CORE_IDENTIFIERS.index,
                    Visibility::Public,
                    builder.create_fn_ty_term(
                        builder.create_params(
                            [
                                builder.create_param(
                                    CORE_IDENTIFIERS.self_i,
                                    builder.create_var_term(CORE_IDENTIFIERS.Self_i),
                                ),
                                builder.create_param(
                                    CORE_IDENTIFIERS.index,
                                    builder.create_var_term(CORE_IDENTIFIERS.Index),
                                ),
                            ],
                            ParamOrigin::Fn,
                        ),
                        builder.create_var_term(CORE_IDENTIFIERS.Output),
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
                    CORE_IDENTIFIERS.Self_i,
                    Visibility::Public,
                    ty_term,
                    builder.create_app_ty_fn_term(
                        builder.create_var_term(CORE_IDENTIFIERS.List),
                        builder.create_args(
                            [builder
                                .create_nameless_arg(builder.create_var_term(CORE_IDENTIFIERS.T))],
                            ParamOrigin::TyFn,
                        ),
                    ),
                ),
                Member::open_constant(
                    CORE_IDENTIFIERS.Index,
                    Visibility::Public,
                    ty_term,
                    // @@Todo: change this to use usize once we have a better way of inferring
                    // numerics.
                    builder.create_nominal_def_term(i32_ty),
                ),
                Member::open_constant(
                    CORE_IDENTIFIERS.Output,
                    Visibility::Public,
                    ty_term,
                    builder.create_var_term(CORE_IDENTIFIERS.T),
                ),
                Member::open_constant(
                    CORE_IDENTIFIERS.index,
                    Visibility::Public,
                    builder.create_fn_ty_term(
                        builder.create_params(
                            [
                                builder.create_param(
                                    CORE_IDENTIFIERS.self_i,
                                    builder.create_var_term(CORE_IDENTIFIERS.Self_i),
                                ),
                                builder.create_param(
                                    CORE_IDENTIFIERS.index,
                                    builder.create_var_term(CORE_IDENTIFIERS.Index),
                                ),
                            ],
                            ParamOrigin::Fn,
                        ),
                        builder.create_var_term(CORE_IDENTIFIERS.Output),
                    ),
                    builder.create_fn_lit_term(
                        builder.create_fn_ty_term(
                            builder.create_params(
                                [
                                    builder.create_param(
                                        CORE_IDENTIFIERS.self_i,
                                        builder.create_var_term(CORE_IDENTIFIERS.Self_i),
                                    ),
                                    builder.create_param(
                                        CORE_IDENTIFIERS.index,
                                        builder.create_var_term(CORE_IDENTIFIERS.Index),
                                    ),
                                ],
                                ParamOrigin::Fn,
                            ),
                            builder.create_var_term(CORE_IDENTIFIERS.Output),
                        ),
                        builder.create_rt_term(builder.create_var_term(CORE_IDENTIFIERS.Output)),
                    ),
                ),
            ],
        ),
    );
    let _list_ty_fn = builder.create_ty_fn_term(
        Some(CORE_IDENTIFIERS.List),
        builder
            .create_params([builder.create_param(CORE_IDENTIFIERS.T, ty_term)], ParamOrigin::TyFn),
        ty_term,
        builder.create_merge_term([
            builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
            builder.create_mod_def_term(list_index_impl),
        ]),
    );

    let _set_ty_fn = builder.create_ty_fn_term(
        Some(CORE_IDENTIFIERS.Set),
        builder.create_params(
            [builder.create_param(
                CORE_IDENTIFIERS.T,
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
        Some(CORE_IDENTIFIERS.Map),
        builder.create_params(
            [
                builder.create_param(
                    CORE_IDENTIFIERS.K,
                    builder.create_merge_term([
                        builder.create_trt_term(hash_trt),
                        builder.create_trt_term(eq_trt),
                    ]),
                ),
                builder.create_param(CORE_IDENTIFIERS.V, ty_term),
            ],
            ParamOrigin::TyFn,
        ),
        ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
}
