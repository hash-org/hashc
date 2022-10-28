//! Contains all the core type and trait definitions of the language.
//!
//! These are accessed during the AST traversal in order to type certain
//! language primitives (for example `if`-block subjects). This is because a lot
//! of the primitive Hash types aren't actually primitives as
//! far as the typechecker is concerned. This includes: integers, floats,
//! characters, strings, lists, maps, references, etc.
use hash_ast::ast::ParamOrigin;
use hash_source::identifier::IDENTS;

use crate::{
    builder::PrimitiveBuilder,
    mods::ModDefOriginOld,
    scope::{Member, ScopeKind, Visibility},
    storage::GlobalStorage,
};

/// Create the core language type and trait definitions in the given
/// [GlobalStorage], and add their symbols to the root scope.
pub fn create_core_defs_in(global_storage: &GlobalStorage) {
    // @@Safety: core defs have not been filled in global_storage, don't access
    // global_storage.core_defs()!
    //
    // We use the root scope as the population scope, since these are the core
    // definitions.
    let builder = PrimitiveBuilder::new_with_scope(global_storage, global_storage.root_scope);

    // Marker trait for types that are runtime instantiable
    // We call this IDENTS.Type because that's what people usually mean
    // when they say IDENTS.type.
    builder.add_pub_member_to_scope(
        IDENTS.Type,
        builder.create_trt_kind_term(),
        builder.create_sized_ty_term(),
    );

    // Primitive integers
    let _i8_ty = builder.create_opaque_struct_def(IDENTS.i8);

    let _i16_ty = builder.create_opaque_struct_def(IDENTS.i16);
    let i32_ty = builder.create_opaque_struct_def(IDENTS.i32);
    let _i64_ty = builder.create_opaque_struct_def(IDENTS.i64);
    let _isize_ty = builder.create_opaque_struct_def(IDENTS.isize);
    let _ibig_ty = builder.create_opaque_struct_def(IDENTS.ibig);

    let _u8_ty = builder.create_opaque_struct_def(IDENTS.u8);
    let _u16_ty = builder.create_opaque_struct_def(IDENTS.u16);
    let _u32_ty = builder.create_opaque_struct_def(IDENTS.u32);
    let u64_ty = builder.create_opaque_struct_def(IDENTS.u64);
    let _usize_ty = builder.create_opaque_struct_def(IDENTS.usize);
    let _ubig_ty = builder.create_opaque_struct_def(IDENTS.ubig);

    let _f32_ty = builder.create_opaque_struct_def(IDENTS.f32);
    let _f64_ty = builder.create_opaque_struct_def(IDENTS.f64);

    // Char and bool
    let _char_ty = builder.create_opaque_struct_def(IDENTS.char);
    let bool_ty = builder.create_enum_def(
        Some(IDENTS.bool),
        [
            builder.create_constant_enum_variant(IDENTS.r#true),
            builder.create_constant_enum_variant(IDENTS.r#false),
        ],
    );
    let bool_ty_term = builder.create_nominal_def_term(bool_ty);
    builder.add_pub_member_to_scope(
        IDENTS.r#true,
        bool_ty_term,
        builder.create_enum_variant_value_term(IDENTS.r#true, bool_ty),
    );
    builder.add_pub_member_to_scope(
        IDENTS.r#false,
        bool_ty_term,
        builder.create_enum_variant_value_term(IDENTS.r#false, bool_ty),
    );

    // String
    let _str_ty = builder.create_opaque_struct_def(IDENTS.str);

    let sized_ty_term = builder.create_sized_ty_term();

    // Any type
    let any_ty = builder.create_any_ty_term();
    builder.add_pub_member_to_scope(IDENTS.AnyType, builder.create_trt_kind_term(), any_ty);

    // Never type
    let never_ty = builder.create_never_ty();
    builder.add_pub_member_to_scope(IDENTS.never, builder.create_sized_ty_term(), never_ty);

    // Void type
    let void_ty = builder.create_void_ty_term();
    builder.add_pub_member_to_scope(IDENTS.void, builder.create_sized_ty_term(), void_ty);

    // Reference types
    let _reference_ty_fn = builder.create_ty_fn_term(
        Some(IDENTS.Ref),
        builder.create_params([builder.create_param(IDENTS.T, sized_ty_term)], ParamOrigin::TyFn),
        sized_ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
    let _reference_mut_ty_fn = builder.create_ty_fn_term(
        Some(IDENTS.RefMut),
        builder.create_params([builder.create_param(IDENTS.T, sized_ty_term)], ParamOrigin::TyFn),
        sized_ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
    let _raw_reference_ty_fn = builder.create_ty_fn_term(
        Some(IDENTS.RawRef),
        builder.create_params([builder.create_param(IDENTS.T, sized_ty_term)], ParamOrigin::TyFn),
        sized_ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
    let _raw_reference_mut_ty_fn = builder.create_ty_fn_term(
        Some(IDENTS.RawRefMut),
        builder.create_params([builder.create_param(IDENTS.T, sized_ty_term)], ParamOrigin::TyFn),
        sized_ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );

    // @@Incomplete: these traits should take ref self, not self.

    // Hash and Eq traits
    let hash_trt = builder.create_trt_def(
        Some(IDENTS.Hash),
        builder.create_scope(
            ScopeKind::Trait,
            [
                Member::uninitialised_constant(IDENTS.Self_i, Visibility::Public, sized_ty_term),
                Member::uninitialised_constant(
                    IDENTS.hash,
                    Visibility::Public,
                    builder.create_fn_ty_term(
                        builder.create_params(
                            [builder.create_param(
                                IDENTS.value,
                                builder.create_var_term(IDENTS.Self_i),
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
        Some(IDENTS.Eq),
        builder.create_scope(
            ScopeKind::Trait,
            [
                Member::uninitialised_constant(IDENTS.Self_i, Visibility::Public, sized_ty_term),
                Member::uninitialised_constant(
                    IDENTS.eq,
                    Visibility::Public,
                    builder.create_fn_ty_term(
                        builder.create_params(
                            [
                                builder
                                    .create_param(IDENTS.a, builder.create_var_term(IDENTS.Self_i)),
                                builder
                                    .create_param(IDENTS.b, builder.create_var_term(IDENTS.Self_i)),
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
        Some(IDENTS.Index),
        builder.create_scope(
            ScopeKind::Trait,
            [
                Member::uninitialised_constant(IDENTS.Self_i, Visibility::Public, sized_ty_term),
                Member::uninitialised_constant(IDENTS.Index, Visibility::Public, sized_ty_term),
                Member::uninitialised_constant(IDENTS.Output, Visibility::Public, sized_ty_term),
                Member::uninitialised_constant(
                    IDENTS.index,
                    Visibility::Public,
                    builder.create_fn_ty_term(
                        builder.create_params(
                            [
                                builder.create_param(
                                    IDENTS.self_i,
                                    builder.create_var_term(IDENTS.Self_i),
                                ),
                                builder.create_param(
                                    IDENTS.index,
                                    builder.create_var_term(IDENTS.Index),
                                ),
                            ],
                            ParamOrigin::Fn,
                        ),
                        builder.create_var_term(IDENTS.Output),
                    ),
                ),
            ],
        ),
    );

    // Collection types
    let index_trt_term = builder.create_trt_term(index_trt);
    let list_index_impl = builder.create_nameless_mod_def(
        ModDefOriginOld::TrtImpl(index_trt_term),
        builder.create_scope(
            ScopeKind::Impl,
            [
                Member::open_constant(
                    IDENTS.Self_i,
                    Visibility::Public,
                    sized_ty_term,
                    builder.create_app_ty_fn_term(
                        builder.create_var_term(IDENTS.List),
                        builder.create_args(
                            [builder.create_nameless_arg(builder.create_var_term(IDENTS.T))],
                            ParamOrigin::TyFn,
                        ),
                    ),
                ),
                Member::open_constant(
                    IDENTS.Index,
                    Visibility::Public,
                    sized_ty_term,
                    // @@Todo: change this to use usize once we have a better way of inferring
                    // numerics.
                    builder.create_nominal_def_term(i32_ty),
                ),
                Member::open_constant(
                    IDENTS.Output,
                    Visibility::Public,
                    sized_ty_term,
                    builder.create_var_term(IDENTS.T),
                ),
                Member::open_constant(
                    IDENTS.index,
                    Visibility::Public,
                    builder.create_fn_ty_term(
                        builder.create_params(
                            [
                                builder.create_param(
                                    IDENTS.self_i,
                                    builder.create_var_term(IDENTS.Self_i),
                                ),
                                builder.create_param(
                                    IDENTS.index,
                                    builder.create_var_term(IDENTS.Index),
                                ),
                            ],
                            ParamOrigin::Fn,
                        ),
                        builder.create_var_term(IDENTS.Output),
                    ),
                    builder.create_fn_lit_term(
                        Some(IDENTS.index),
                        builder.create_fn_ty_term(
                            builder.create_params(
                                [
                                    builder.create_param(
                                        IDENTS.self_i,
                                        builder.create_var_term(IDENTS.Self_i),
                                    ),
                                    builder.create_param(
                                        IDENTS.index,
                                        builder.create_var_term(IDENTS.Index),
                                    ),
                                ],
                                ParamOrigin::Fn,
                            ),
                            builder.create_var_term(IDENTS.Output),
                        ),
                        builder.create_rt_term(builder.create_var_term(IDENTS.Output)),
                    ),
                ),
            ],
        ),
    );
    let _list_ty_fn = builder.create_ty_fn_term(
        Some(IDENTS.List),
        builder.create_params([builder.create_param(IDENTS.T, sized_ty_term)], ParamOrigin::TyFn),
        sized_ty_term,
        builder.create_merge_term([
            builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
            builder.create_mod_def_term(list_index_impl),
        ]),
    );

    let _set_ty_fn = builder.create_ty_fn_term(
        Some(IDENTS.Set),
        builder.create_params(
            [builder.create_param(
                IDENTS.T,
                builder.create_merge_term([
                    builder.create_trt_term(hash_trt),
                    builder.create_trt_term(eq_trt),
                ]),
            )],
            ParamOrigin::TyFn,
        ),
        sized_ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );

    let _map_ty_fn = builder.create_ty_fn_term(
        Some(IDENTS.Map),
        builder.create_params(
            [
                builder.create_param(
                    IDENTS.K,
                    builder.create_merge_term([
                        builder.create_trt_term(hash_trt),
                        builder.create_trt_term(eq_trt),
                    ]),
                ),
                builder.create_param(IDENTS.V, sized_ty_term),
            ],
            ParamOrigin::TyFn,
        ),
        sized_ty_term,
        builder.create_nominal_def_term(builder.create_nameless_opaque_struct_def()),
    );
}
