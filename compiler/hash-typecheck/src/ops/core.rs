//! Functionality related to determining properties about terms and other
//! constructs.
use hash_source::identifier::{Identifier, CORE_IDENTIFIERS};
use hash_utils::store::Store;

use super::AccessToOps;
use crate::storage::{primitives::Member, terms::TermId, AccessToStorage, StorageRef};

pub struct CoreDefReader<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for CoreDefReader<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> CoreDefReader<'tc> {
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Resolve the given core definition by name.
    ///
    /// Panics if the core definition doesn't exist.
    pub fn resolve_core_def(&self, var_name: Identifier) -> TermId {
        let root_scope = self.global_storage().root_scope;
        let (resolved, index) = self
            .scope_store()
            .map_fast(root_scope, |scope| scope.get(var_name))
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

    pub fn str_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.str)
    }

    pub fn list_ty_fn(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.List)
    }

    pub fn map_ty_fn(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Map)
    }

    pub fn set_ty_fn(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Set)
    }

    pub fn i8_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.i8)
    }

    pub fn i16_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.i16)
    }

    pub fn i32_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.i32)
    }

    pub fn i64_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.i64)
    }

    pub fn isize_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.isize)
    }

    pub fn ibig_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.ibig)
    }

    pub fn u8_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.u8)
    }

    pub fn u16_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.u16)
    }

    pub fn u32_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.u32)
    }

    pub fn u64_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.u64)
    }

    pub fn usize_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.usize)
    }

    pub fn ubig_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.ubig)
    }

    pub fn f32_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.f32)
    }

    pub fn f64_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.f64)
    }

    pub fn char_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.char)
    }

    pub fn bool_ty(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.bool)
    }

    pub fn reference_ty_fn(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Ref)
    }

    pub fn reference_mut_ty_fn(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.RefMut)
    }

    pub fn raw_reference_ty_fn(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.RawRefMut)
    }

    pub fn raw_reference_mut_ty_fn(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.RawRefMut)
    }

    pub fn hash_trt(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Hash)
    }

    pub fn eq_trt(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Eq)
    }

    pub fn index_trt(&self) -> TermId {
        self.resolve_core_def(CORE_IDENTIFIERS.Index)
    }
}
