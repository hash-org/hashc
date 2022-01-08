use std::{collections::HashMap, path::PathBuf};

use hash_utils::counter;

counter! {
    name: ModuleIdx,
    counter_name: MODULE_COUNTER,
    visibility: pub,
    method_visibility: pub,
}

#[derive(Debug)]
pub struct SourceModule {
    path: PathBuf,
    content: String,
}

impl SourceModule {
    pub fn new(path: PathBuf, content: String) -> Self {
        Self { path, content }
    }

    pub fn content(&self) -> &str {
        todo!()
    }

    pub fn filename(&self) -> PathBuf {
        todo!()
    }
}

#[derive(Debug)]
pub struct SourceMap {
    map: HashMap<ModuleIdx, SourceModule>,
}

impl SourceMap {
    pub fn get(&self, index: ModuleIdx) -> SourceModule {
        todo!()
    }
}
