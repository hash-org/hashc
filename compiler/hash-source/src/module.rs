use std::path::Path;

use hash_utils::counter;
use lazy_static::lazy_static;

counter! {
    name: ModuleIdx,
    counter_name: MODULE_COUNTER,
    visibility: pub,
    method_visibility: pub,
}

lazy_static! {
    pub static ref INTERACTIVE_MODULE: ModuleIdx = ModuleIdx::new();
}

pub trait SourceMap {
    fn path_by_index(&self, index: ModuleIdx) -> &Path;
    fn contents_by_index(&self, index: ModuleIdx) -> &str;
}
