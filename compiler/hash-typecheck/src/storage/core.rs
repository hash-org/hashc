//! Contains all the core type and trait definitions of the language.
//!
//! These are accessed during the AST traversal in order to type certain language primitives (for
//! example `if`-block subjects). This is because a lot of the "primitive" Hash types aren't
//! actually primitives as far as the typechecker is concerned. This includes: integers, floats,
//! characters, strings, lists, maps, references, etc.
use super::{
    primitives::{NominalDefId, TrtDefId, ValueId},
    GlobalStorage,
};
use crate::ops::building::PrimitiveBuilder;

/// Contains all the core type and trait definitions of the language.
#[derive(Debug, Clone)]
pub struct CoreDefs {
    pub str_ty: NominalDefId,
    pub list_ty_fn: ValueId,
    pub map_ty_fn: ValueId,
    pub set_ty_fn: ValueId,
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
    pub reference_ty_fn: ValueId,
    pub raw_reference_ty_fn: ValueId,
    pub hash_trt: TrtDefId,
    pub eq_trt: TrtDefId,
}

impl CoreDefs {
    /// Create the core language type and trait definitions in the given [GlobalStorage], and add
    /// their symbols to the root scope.
    pub fn new(global_storage: &mut GlobalStorage) -> Self {
        // @@Safety: core defs have not been filled in global_storage, don't access
        // global_storage.core_defs()!
        //
        // We use the root scope as the population scope, since these are the core definitions.
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
            "bool",
            [
                builder.create_enum_variant("true", []),
                builder.create_enum_variant("false", []),
            ],
        );

        // String
        let str_ty = builder.create_opaque_struct_def("str");

        // Reference types
        let reference_ty_fn = builder.create_ty_fn_value(
            "Ref",
            [builder.create_param("T", builder.create_ty_of_ty())],
            builder.create_ty_of_ty(),
            builder.create_nominal_value(builder.create_nameless_opaque_struct_def()),
        );
        let raw_reference_ty_fn = builder.create_ty_fn_value(
            "RawRef",
            [builder.create_param("T", builder.create_ty_of_ty())],
            builder.create_ty_of_ty(),
            builder.create_nominal_value(builder.create_nameless_opaque_struct_def()),
        );

        // Handy shorthand for &Self type
        let ref_self_ty = builder.create_app_ty_fn_ty(
            reference_ty_fn,
            [builder.create_arg("T", builder.create_ty_value(builder.create_var_ty("Self")))],
        );

        // Hash and Eq traits
        let hash_trt = builder.create_trait_def(
            "Hash",
            [builder.create_unset_pub_member(
                "hash",
                builder.create_fn_ty(
                    [builder.create_param("value", ref_self_ty)],
                    builder.create_nominal_ty(u64_ty),
                ),
            )],
        );
        let eq_trt = builder.create_trait_def(
            "Eq",
            [builder.create_unset_pub_member(
                "eq",
                builder.create_fn_ty(
                    [
                        builder.create_param("a", ref_self_ty),
                        builder.create_param("b", ref_self_ty),
                    ],
                    builder.create_nominal_ty(u64_ty),
                ),
            )],
        );

        // Collection types
        let list_ty_fn = builder.create_ty_fn_value(
            "List",
            [builder.create_param("T", builder.create_ty_of_ty())],
            builder.create_ty_of_ty(),
            builder.create_nominal_value(builder.create_nameless_opaque_struct_def()),
        );

        let set_ty_fn = builder.create_ty_fn_value(
            "Set",
            [builder.create_param("T", builder.create_ty_of_ty())],
            builder.create_ty_of_ty(),
            builder.create_nominal_value(builder.create_nameless_opaque_struct_def()),
        );

        let map_ty_fn = builder.create_ty_fn_value(
            "Map",
            [
                builder.create_param(
                    "K",
                    builder.create_merge_ty([
                        builder.create_ty_of_ty_with_bound(hash_trt),
                        builder.create_ty_of_ty_with_bound(eq_trt),
                    ]),
                ),
                builder.create_param("V", builder.create_ty_of_ty()),
            ],
            builder.create_ty_of_ty(),
            builder.create_nominal_value(builder.create_nameless_opaque_struct_def()),
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
            reference_ty_fn,
            raw_reference_ty_fn,
            hash_trt,
            eq_trt,
        }
    }
}
