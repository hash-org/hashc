//! Functionality related to determining properties about terms and other
//! constructs.
use hash_source::identifier::{Identifier, IDENTS};
use hash_tir::{scope::Member, terms::TermId};
use hash_utils::store::Store;

use super::AccessToOps;
use crate::storage::{AccessToStorage, StorageRef};

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
        let root_scope = self.root_scope();

        let (resolved, index) = self
            .scope_store()
            .map_fast(root_scope, |scope| scope.get(var_name))
            .unwrap_or_else(|| panic!("Failed to find core def: {var_name}"));
        match resolved {
            Member::Constant(_) | Member::Variable(_) => {
                self.builder().create_scope_var_term(var_name, root_scope, index)
            }
            Member::Bound(_) | Member::SetBound(_) => {
                panic!("Core def {var_name} found to be invalid member: {resolved:?}")
            }
        }
    }

    pub fn str_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.str)
    }

    pub fn array_ty(&self) -> TermId {
        todo!()
    }

    pub fn i8_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.i8)
    }

    pub fn i16_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.i16)
    }

    pub fn i32_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.i32)
    }

    pub fn i64_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.i64)
    }

    pub fn isize_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.isize)
    }

    pub fn ibig_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.ibig)
    }

    pub fn u8_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.u8)
    }

    pub fn u16_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.u16)
    }

    pub fn u32_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.u32)
    }

    pub fn u64_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.u64)
    }

    pub fn usize_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.usize)
    }

    pub fn ubig_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.ubig)
    }

    pub fn f32_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.f32)
    }

    pub fn f64_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.f64)
    }

    pub fn char_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.char)
    }

    pub fn bool_ty(&self) -> TermId {
        self.resolve_core_def(IDENTS.bool)
    }

    pub fn reference_ty_fn(&self) -> TermId {
        self.resolve_core_def(IDENTS.Ref)
    }

    pub fn reference_mut_ty_fn(&self) -> TermId {
        self.resolve_core_def(IDENTS.RefMut)
    }

    pub fn raw_reference_ty_fn(&self) -> TermId {
        self.resolve_core_def(IDENTS.RawRefMut)
    }

    pub fn raw_reference_mut_ty_fn(&self) -> TermId {
        self.resolve_core_def(IDENTS.RawRefMut)
    }

    pub fn hash_trt(&self) -> TermId {
        self.resolve_core_def(IDENTS.Hash)
    }

    pub fn eq_trt(&self) -> TermId {
        self.resolve_core_def(IDENTS.Eq)
    }

    pub fn index_trt(&self) -> TermId {
        self.resolve_core_def(IDENTS.Index)
    }
}
