use hash_ast::module::ModuleIdx;
use crate::types::TypeId;

#[derive(Debug)]
pub struct TypecheckState {
    pub in_loop: bool,
    pub ret_once: bool,
    pub func_ret_type: Option<TypeId>,
    pub current_module: ModuleIdx,
}

impl Default for TypecheckState {
    fn default() -> Self {
        Self {
            in_loop: false,
            ret_once: false,
            func_ret_type: None,
            current_module: ModuleIdx(0),
        }
    }
}
