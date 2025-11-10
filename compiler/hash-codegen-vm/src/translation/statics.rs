//! Implementation of the `StaticMethods` trait for the `CodeGenCtx` struct in
//! the LLVM backend.

use hash_codegen::{target::alignment::Alignment, traits::statics::StaticMethods};

use crate::ctx::Ctx;

impl StaticMethods for Ctx<'_> {
    fn static_addr_of(&self, _cv: Self::Value, _align: Alignment) -> Self::Value {
        todo!()
    }
}
