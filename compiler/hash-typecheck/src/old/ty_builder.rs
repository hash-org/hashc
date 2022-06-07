use hash_ast::ident::IDENTIFIER_MAP;
use hash_source::location::SourceLocation;

use crate::storage::{
    common::{
        FnTy, FnTyId, NamedTy, NamedTyId, SpecificTyId, TupleTy, TupleTyId, TyDefId, TyId, TyValue,
        UnionTy, UnionTyId, UnresolvedTy, VarTyId,
    },
    ty_vars::TyVar,
    GlobalStorage,
};

pub struct TyBuilder<'gs> {
    pub global_storage: &'gs mut GlobalStorage,
}

macro_rules! core_def_creator_no_args {
    ($fn_name:ident, $def_name:ident) => {
        pub fn $fn_name(&mut self, location: Option<SourceLocation>) -> NamedTyId {
            self.create_named_ty_no_args(self.global_storage.core_defs.$def_name, location)
        }
    };
}

impl<'gs> TyBuilder<'gs> {
    pub fn create_var_ty(&mut self, name: &str, location: Option<SourceLocation>) -> VarTyId {
        VarTyId::from_ty_id_unchecked(self.global_storage.ty_store.create(
            TyValue::Var(TyVar {
                name: IDENTIFIER_MAP.create_ident(name),
            }),
            location,
        ))
    }

    pub fn create_unresolved_ty(&mut self, location: Option<SourceLocation>) -> TyId {
        let data_id = self.global_storage.ty_store.create_unresolved();
        self.global_storage
            .ty_store
            .create(TyValue::Unresolved(UnresolvedTy { id: data_id }), location)
    }

    pub fn create_tuple_ty(
        &mut self,
        types: Vec<TyId>,
        location: Option<SourceLocation>,
    ) -> TupleTyId {
        TupleTyId::from_ty_id_unchecked(
            self.global_storage
                .ty_store
                .create(TyValue::Tuple(TupleTy { types }), location),
        )
    }

    pub fn create_void_ty(&mut self, location: Option<SourceLocation>) -> TupleTyId {
        self.create_tuple_ty(vec![], location)
    }

    pub fn create_never_ty(&mut self, location: Option<SourceLocation>) -> UnionTyId {
        UnionTyId::from_ty_id_unchecked(
            self.global_storage
                .ty_store
                .create(TyValue::Union(UnionTy { variants: vec![] }), location),
        )
    }

    pub fn create_fn_ty(
        &mut self,
        args: Vec<TyId>,
        return_ty: TyId,
        location: Option<SourceLocation>,
    ) -> FnTyId {
        FnTyId::from_ty_id_unchecked(
            self.global_storage
                .ty_store
                .create(TyValue::Fn(FnTy { args, return_ty }), location),
        )
    }

    pub fn create_named_ty(
        &mut self,
        def_id: TyDefId,
        args: Vec<TyId>,
        location: Option<SourceLocation>,
    ) -> NamedTyId {
        NamedTyId::from_ty_id_unchecked(
            self.global_storage
                .ty_store
                .create(TyValue::Named(NamedTy { def_id, args }), location),
        )
    }

    pub fn create_named_ty_no_args(
        &mut self,
        def_id: TyDefId,
        location: Option<SourceLocation>,
    ) -> NamedTyId {
        self.create_named_ty(def_id, vec![], location)
    }

    core_def_creator_no_args!(create_str_ty, str_ty);
    core_def_creator_no_args!(create_i8_ty, i8_ty);
    core_def_creator_no_args!(create_i16_ty, i16_ty);
    core_def_creator_no_args!(create_i32_ty, i32_ty);
    core_def_creator_no_args!(create_i64_ty, i64_ty);
    core_def_creator_no_args!(create_u8_ty, u8_ty);
    core_def_creator_no_args!(create_u16_ty, u16_ty);
    core_def_creator_no_args!(create_u32_ty, u32_ty);
    core_def_creator_no_args!(create_u64_ty, u64_ty);
    core_def_creator_no_args!(create_f32_ty, f32_ty);
    core_def_creator_no_args!(create_f64_ty, f64_ty);
    core_def_creator_no_args!(create_char_ty, char_ty);
    core_def_creator_no_args!(create_bool_ty, bool_ty);

    pub fn create_list_ty(&mut self, el_ty: TyId, location: Option<SourceLocation>) -> NamedTyId {
        self.create_named_ty(self.global_storage.core_defs.list_ty, vec![el_ty], location)
    }

    pub fn create_set_ty(&mut self, el_ty: TyId, location: Option<SourceLocation>) -> NamedTyId {
        self.create_named_ty(self.global_storage.core_defs.set_ty, vec![el_ty], location)
    }

    pub fn create_map_ty(
        &mut self,
        key_ty: TyId,
        value_ty: TyId,
        location: Option<SourceLocation>,
    ) -> NamedTyId {
        self.create_named_ty(
            self.global_storage.core_defs.map_ty,
            vec![key_ty, value_ty],
            location,
        )
    }

    pub fn create_ref_ty(&mut self, inner_ty: TyId, location: Option<SourceLocation>) -> NamedTyId {
        self.create_named_ty(
            self.global_storage.core_defs.reference_ty,
            vec![inner_ty],
            location,
        )
    }

    pub fn create_raw_ref_ty(
        &mut self,
        inner_ty: TyId,
        location: Option<SourceLocation>,
    ) -> NamedTyId {
        self.create_named_ty(
            self.global_storage.core_defs.raw_reference_ty,
            vec![inner_ty],
            location,
        )
    }
}
