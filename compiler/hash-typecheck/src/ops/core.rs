//! Functionality related to determining properties about terms and other
//! constructs.
use hash_source::identifier::{Identifier, CORE_IDENTIFIERS};

use crate::storage::{
    primitives::{Member, TermId},
    AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
};

use super::AccessToOpsMut;

pub struct CoreDefReader<'tc> {
    storage: StorageRefMut<'tc>,
}

impl<'tc> AccessToStorage for CoreDefReader<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> AccessToStorageMut for CoreDefReader<'tc> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'tc> CoreDefReader<'tc> {
    pub fn new(storage: StorageRefMut<'tc>) -> Self {
        Self { storage }
    }

    fn resolve_core_def(&mut self, var_name: Identifier) -> TermId {
        let root_scope = self.global_storage().root_scope;
        let (resolved, index) = self
            .scope_store()
            .get(root_scope)
            .get(var_name)
            .unwrap_or_else(|| panic!("Failed to find core def: {}", var_name));
        match resolved {
            Member::Constant(_) | Member::Variable(_) => {
                self.builder().create_scope_var_term(var_name, root_scope, index)
            }
            Member::Bound(_) | Member::SetBound(_) => {
                panic!("Core def {} found to be invalid member: {:?}", var_name, resolved)
            }
        }
    }

    pub fn str_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.str)
    }

    pub fn list_ty_fn(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.List)
    }

    pub fn map_ty_fn(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Map)
    }

    pub fn set_ty_fn(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Set)
    }

    pub fn i8_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.i8)
    }

    pub fn i16_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.i16)
    }

    pub fn i32_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.i32)
    }

    pub fn i64_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.i64)
    }

    pub fn u8_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.u8)
    }

    pub fn u16_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.u16)
    }

    pub fn u32_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.u32)
    }

    pub fn u64_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.u64)
    }

    pub fn f32_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.f32)
    }

    pub fn f64_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.f64)
    }

    pub fn char_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.char)
    }

    pub fn bool_ty(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.bool)
    }

    pub fn reference_ty_fn(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Ref)
    }

    pub fn reference_mut_ty_fn(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.RefMut)
    }

    pub fn raw_reference_ty_fn(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.RawRefMut)
    }

    pub fn raw_reference_mut_ty_fn(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.RawRefMut)
    }

    pub fn hash_trt(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Hash)
    }

    pub fn eq_trt(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Eq)
    }

    pub fn index_trt(&mut self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Index)
    }
}
