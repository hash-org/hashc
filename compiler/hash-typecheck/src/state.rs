//! All rights reserved 2022 (c) The Hash Language authors
use hash_source::SourceId;

use crate::types::TypeId;

#[derive(Debug)]
pub struct TypecheckState {
    pub in_loop: bool,
    pub in_bound_def: bool,
    pub ret_once: bool,
    pub func_ret_type: Option<TypeId>,
    pub current_module: SourceId,
}

impl TypecheckState {
    pub fn new(current_module: SourceId) -> Self {
        Self {
            in_loop: false,
            in_bound_def: false,
            ret_once: false,
            func_ret_type: None,
            current_module,
        }
    }
}
