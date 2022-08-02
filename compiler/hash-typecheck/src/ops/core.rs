//! Functionality related to determining properties about terms and other
//! constructs.
use crate::storage::{primitives::TermId, AccessToStorage, StorageRef};

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

    pub fn str_ty(&self) -> TermId {
        todo!()
    }
    pub fn list_ty_fn(&self) -> TermId {
        todo!()
    }
    pub fn map_ty_fn(&self) -> TermId {
        todo!()
    }
    pub fn set_ty_fn(&self) -> TermId {
        todo!()
    }
    pub fn i8_ty(&self) -> TermId {
        todo!()
    }
    pub fn i16_ty(&self) -> TermId {
        todo!()
    }
    pub fn i32_ty(&self) -> TermId {
        todo!()
    }
    pub fn i64_ty(&self) -> TermId {
        todo!()
    }
    pub fn u8_ty(&self) -> TermId {
        todo!()
    }
    pub fn u16_ty(&self) -> TermId {
        todo!()
    }
    pub fn u32_ty(&self) -> TermId {
        todo!()
    }
    pub fn u64_ty(&self) -> TermId {
        todo!()
    }
    pub fn f32_ty(&self) -> TermId {
        todo!()
    }
    pub fn f64_ty(&self) -> TermId {
        todo!()
    }
    pub fn char_ty(&self) -> TermId {
        todo!()
    }
    pub fn bool_ty(&self) -> TermId {
        todo!()
    }
    pub fn any_ty(&self) -> TermId {
        todo!()
    }
    pub fn reference_ty_fn(&self) -> TermId {
        todo!()
    }
    pub fn reference_mut_ty_fn(&self) -> TermId {
        todo!()
    }
    pub fn raw_reference_ty_fn(&self) -> TermId {
        todo!()
    }
    pub fn raw_reference_mut_ty_fn(&self) -> TermId {
        todo!()
    }
    pub fn hash_trt(&self) -> TermId {
        todo!()
    }
    pub fn eq_trt(&self) -> TermId {
        todo!()
    }
    pub fn index_trt(&self) -> TermId {
        todo!()
    }
    pub fn runtime_instantiable_trt(&self) -> TermId {
        todo!()
    }
}
