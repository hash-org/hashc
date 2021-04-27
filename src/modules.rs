pub type ModuleIdx = usize;

pub struct Module<'a> {
    idx: usize,
    modules: &'a Modules,
}

impl Module<'_> {
    pub fn content(&self) -> &str {
        self.modules.contents[self.idx].as_ref()
    }

    pub fn filename(&self) -> &str {
        self.modules.filenames[self.idx].as_ref()
    }
}

pub struct Modules {
    filenames: Vec<String>,
    contents: Vec<String>,
}

impl Modules {
    pub fn get_module<'a>(&'a self, idx: usize) -> Module<'a> {
        Module { idx, modules: self }
    }
}
