//! Contains all the core type and trait definitions of the language.
use super::{
    nominals::NominalDefStore,
    primitives::{NominalDef, NominalDefId, TrtDefId},
    scope::Scope,
    trts::TrtDefStore,
    tys::TyStore,
};
use crate::storage::primitives::StructDef;
use hash_ast::ident::IDENTIFIER_MAP;

/// Contains all the core type and trait definitions of the language.
pub struct CoreDefs {
    pub str_ty: NominalDefId,
    pub list_ty: NominalDefId,
    pub map_ty: NominalDefId,
    pub set_ty: NominalDefId,
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
    pub reference_ty: NominalDefId,
    pub raw_reference_ty: NominalDefId,
    pub hash_trt: TrtDefId,
    pub eq_trt: TrtDefId,
}

impl CoreDefs {
    /// Create the core language type and trait definitions in the given stores, and add their
    /// symbols to the given scope.
    pub fn create(
        nominal_def_store: &mut NominalDefStore,
        ty_store: &mut TyStore,
        trt_def_store: &mut TrtDefStore,
        scope: &mut Scope,
    ) -> Self {
        todo!()
        // Shorthand macros

        // Struct without fields (opaque)
        // macro_rules! opaque_struct_type_def {
        //     (name: $name:expr) => {
        //         opaque_struct_type_def!(name: $name, params: TyParams::empty())
        //     };
        //     (name: $name:expr, params: $params:expr) => {{
        //         let def_id = nominal_def_store.create(
        //             NominalDef::Struct(StructDef {
        //                 name: IDENTIFIER_MAP.create_ident($name),
        //                 params: $params,
        //                 fields: StructFields::opaque(),
        //             }),
        //             None,
        //         );
        //         scope.add_symbol(
        //             IDENTIFIER_MAP.create_ident($name),
        //             SymbolTarget::TyDef(ty_id),
        //         );
        //         ty_id
        //     }};
        // }

        // // Trait
        // macro_rules! trait_def {
        //     (name: $name:expr, params: $params:expr, fn_type: ($fn_args:expr) -> ($fn_return:expr)) => {{
        //         let trt_id = trt_store.create(|id| Trt {
        //             id,
        //             name: IDENTIFIER_MAP.create_ident($name),
        //             params: $params,
        //             fn_ty: FnTyId::from_ty_id_unchecked(ty_store.create(
        //                 TyValue::Fn(FnTy {
        //                     args: $fn_args,
        //                     return_ty: $fn_return,
        //                 }),
        //                 None,
        //             )),
        //         });
        //         scope.add_symbol(
        //             IDENTIFIER_MAP.create_ident($name),
        //             SymbolTarget::Trt(trt_id),
        //         );
        //         trt_id
        //     }};
        // }

        // // Enum without data
        // macro_rules! dataless_enum_type_def {
        //     (name: $name:expr, variants: [$($variant_name:expr),*]) => {{
        //         let ty_id = ty_def_store.create(
        //             TyDefValueKind::Enum(EnumDef {
        //                 name: IDENTIFIER_MAP.create_ident($name),
        //                 params: TyParams::empty(),
        //                 variants: EnumVariants::from_iter([
        //                     $(
        //                         EnumVariant {
        //                             name: IDENTIFIER_MAP.create_ident($variant_name),
        //                             data: vec![],
        //                         },
        //                     )*
        //                 ]),
        //             }),
        //             None,
        //         );
        //         scope.add_symbol(
        //             IDENTIFIER_MAP.create_ident($name),
        //             SymbolTarget::TyDef(ty_id),
        //         );

        //         $(
        //             scope.add_symbol(
        //                 IDENTIFIER_MAP.create_ident($variant_name),
        //                 SymbolTarget::EnumVariant(ty_id),
        //             );
        //         )*

        //         ty_id
        //     }};
        // }

        // // Helper to create type variables
        // let ty_var = |name: &str| {
        //     VarTyId::from_ty_id_unchecked(ty_store.create(
        //         TyValue::Var(TyVar {
        //             name: IDENTIFIER_MAP.create_ident(name),
        //         }),
        //         None,
        //     ))
        // };

        // // Helper to create named types (without type args)
        // let named_ty = |def_id: TyDefId| {
        //     NamedTyId::from_ty_id_unchecked(ty_store.create(
        //         TyValue::Named(NamedTy {
        //             def_id,
        //             args: vec![],
        //         }),
        //         None,
        //     ))
        // };

        // // Integers and other basic primitives
        // let i8_ty = opaque_struct_type_def!(name: "i8");
        // let i16_ty = opaque_struct_type_def!(name: "i16");
        // let i32_ty = opaque_struct_type_def!(name: "i32");
        // let i64_ty = opaque_struct_type_def!(name: "i64");

        // let u8_ty = opaque_struct_type_def!(name: "u8");
        // let u16_ty = opaque_struct_type_def!(name: "u16");
        // let u32_ty = opaque_struct_type_def!(name: "u32");
        // let u64_ty = opaque_struct_type_def!(name: "u64");

        // let f32_ty = opaque_struct_type_def!(name: "f32");
        // let f64_ty = opaque_struct_type_def!(name: "f64");

        // let char_ty = opaque_struct_type_def!(name: "char");
        // let bool_ty = dataless_enum_type_def!(name: "bool", variants: ["true", "false"]);
        // let str_ty = opaque_struct_type_def!(name: "str");

        // // Void type alias
        // scope.add_symbol(
        //     IDENTIFIER_MAP.create_ident("void"),
        //     SymbolTarget::TyAlias(ty_store.create(TyValue::Tuple(TupleTy { types: vec![] }), None)),
        // );

        // // Never type alias
        // scope.add_symbol(
        //     IDENTIFIER_MAP.create_ident("never"),
        //     SymbolTarget::TyAlias(
        //         ty_store.create(TyValue::Union(UnionTy { variants: vec![] }), None),
        //     ),
        // );

        // // References
        // let reference_var = ty_var("T");
        // let reference_ty = opaque_struct_type_def!(
        //     name: "Ref",
        //     params: TyParams {
        //         variables: vec![reference_var],
        //         trt_bounds: vec![],
        //     }
        // );

        // let raw_reference_var = ty_var("T");
        // let raw_reference_ty = opaque_struct_type_def!(
        //     name: "RawRef",
        //     params: TyParams {
        //         variables: vec![raw_reference_var],
        //         trt_bounds: vec![],
        //     }
        // );

        // // Traits for maps and sets
        // let hash_var = ty_var("T");
        // let hash_trt = trait_def!(
        //     name: "hash",
        //     params: TyParams {
        //         variables: vec![hash_var],
        //         trt_bounds: vec![],
        //     },
        //     fn_type: (vec![hash_var.to_ty_id()]) -> (named_ty(u64_ty).to_ty_id())
        // );
        // let eq_var = ty_var("T");
        // let eq_trt = trait_def!(
        //     name: "eq",
        //     params: TyParams {
        //         variables: vec![eq_var],
        //         trt_bounds: vec![],
        //     },
        //     fn_type: (vec![eq_var.to_ty_id(), eq_var.to_ty_id()]) -> (named_ty(bool_ty).to_ty_id())
        // );

        // // Map, list and set
        // let map_key = ty_var("K");
        // let map_value = ty_var("V");
        // let map_ty = opaque_struct_type_def!(
        //     name: "Map",
        //     params: TyParams {
        //         variables: vec![map_key, map_value],
        //         trt_bounds: vec![
        //             TrtBound {
        //                 trt: hash_trt,
        //                 args: vec![map_key.to_ty_id()],
        //             },
        //             TrtBound {
        //                 trt: eq_trt,
        //                 args: vec![map_key.to_ty_id()],
        //             },
        //         ],
        //     }
        // );
        // let list_el = ty_var("T");
        // let list_ty = opaque_struct_type_def!(
        //     name: "List",
        //     params: TyParams {
        //         variables: vec![list_el],
        //         trt_bounds: vec![],
        //     }
        // );
        // let set_el = ty_var("T");
        // let set_ty = opaque_struct_type_def!(
        //     name: "Set",
        //     params: TyParams {
        //         variables: vec![set_el],
        //         trt_bounds: vec![],
        //     }
        // );

        // Self {
        //     str_ty,
        //     map_ty,
        //     list_ty,
        //     set_ty,
        //     i8_ty,
        //     i16_ty,
        //     i32_ty,
        //     i64_ty,
        //     u8_ty,
        //     u16_ty,
        //     u32_ty,
        //     u64_ty,
        //     f32_ty,
        //     f64_ty,
        //     char_ty,
        //     bool_ty,
        //     reference_ty,
        //     raw_reference_ty,
        //     eq_trt,
        //     hash_trt,
        // }
    }
}
