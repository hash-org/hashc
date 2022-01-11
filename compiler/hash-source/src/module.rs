use std::path::Path;

use hash_utils::counter;

counter! {
    name: ModuleIdx,
    counter_name: MODULE_COUNTER,
    visibility: pub,
    method_visibility: pub,
}

pub trait SourceMap {
    fn path_by_index(&self, index: ModuleIdx) -> &Path;
    fn contents_by_index(&self, index: ModuleIdx) -> &str;
}
