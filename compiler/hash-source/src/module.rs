use std::{collections::HashMap, path::{PathBuf, Path}};

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
        self.content.as_str()
    }

    pub fn filename(&self) -> &Path {
        self.path.as_ref()
    }
}

#[derive(Debug)]
pub struct SourceMap {
    map: HashMap<ModuleIdx, SourceModule>,
}

impl SourceMap {
    pub fn new(map: HashMap<ModuleIdx, SourceModule>) -> Self {
        Self {
            map
        }
    }
    pub fn get(&self, index: ModuleIdx) -> &SourceModule {
        self.map.get(&index).unwrap()
    }
}
