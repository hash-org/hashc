//! Module-related containers and utilities.
//
// All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use std::{
    cell::RefCell,
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
};

use crate::{ast, error::ParseError, location::Location};

/// A module identifier which is an index into [Modules].
pub type ModuleIdx = usize;

// FIXME: this is what we should be looking at rather than doing at runtime!
// Module names that are used within the standard library
// const MODULES: &[&Path] = get_stdlib_modules!("./stdlib");

/// The location of a build directory of this package, this used to resolve where the standard library
/// is located at.
static BUILD_DIR: &str = env!("CARGO_MANIFEST_DIR");

/// Name of the prelude module
static PRELUDE: &str = "prelude";

/// Represents an object that is responsible for resolving any module imports
pub struct ModuleResolver {
    map: RefCell<HashMap<PathBuf, ModuleIdx>>,
}

impl ModuleResolver {
    // @@TODO: we should probably pass a modules object into here too
    pub fn new() -> ModuleResolver {
        ModuleResolver {
            map: RefCell::new(HashMap::new()),
        }
    }
    pub fn add_module(&self, _filename: impl AsRef<Path>) {
        unimplemented!()
    }
}

impl Default for ModuleResolver {
    fn default() -> Self {
        Self::new()
    }
}

/// Represents a single module.
pub struct Module<'a> {
    index: ModuleIdx,
    modules: &'a Modules,
}

impl Module<'_> {
    /// Get the content (source text) of the module.
    pub fn content(&self) -> &str {
        self.modules.contents[self.index].as_ref()
    }

    /// Get the filename (full path) of the module.
    pub fn filename(&self) -> &PathBuf {
        &self.modules.filenames[self.index]
    }
}

/// Represents a set of loaded modules.
pub struct Modules {
    pub map: HashMap<PathBuf, ModuleIdx>,
    filenames: Vec<PathBuf>,
    modules: Vec<ast::Module>,
    contents: Vec<String>,
    deps: Vec<Vec<ModuleIdx>>,
}

impl Default for Modules {
    fn default() -> Self {
        Self::new()
    }
}

/// @Incomplete: This will have to change given the fact that we  want to generate this information at compile time.
///              Ideally, we want [`Self::get_stdlib_modules()`] to only generate a vector of pathbufs and the use
///              that to resolve module paths.
impl Modules {
    /// Create a new [Modules] object
    pub fn new() -> Modules {
        Modules {
            map: HashMap::new(),
            modules: vec![],
            deps: vec![],
            filenames: vec![],
            contents: vec![],
        }
    }

    /// Function to add a new module, provided that it is succesfully converted.
    pub fn add(&self, _module: Result<Module, ParseError>) -> Modules {
        unimplemented!()
    }

    pub fn add_module(
        &mut self,
        _node: ast::Module,
        _filename: PathBuf,
        _contents: String,
    ) -> ModuleIdx {
        unimplemented!()
    }

    pub fn add_module_deps(&mut self, _module: ModuleIdx, _deps: impl Iterator<Item = ModuleIdx>) {
        unimplemented!()
    }

    /// Get the module at the given index.
    pub fn get_module(&self, index: ModuleIdx) -> Module<'_> {
        Module {
            index,
            modules: self,
        }
    }

    /// Function that builds a module map of the standard library that is shipped
    /// with the compiler distribution. Standard library modules are referenced
    /// within imports
    pub fn get_stdlib_modules(&self, dir: impl AsRef<Path>) -> Vec<PathBuf> {
        let mut paths: Vec<PathBuf> = Vec::new();

        if dir.as_ref().is_dir() {
            for entry in fs::read_dir(dir).unwrap() {
                match entry {
                    Ok(p) => {
                        let path = p.path();

                        if path.is_dir() {
                            // recurse and get all of the files with the prefix
                            let prefix: &Path = path.file_stem().unwrap().as_ref();

                            for entry in self.get_stdlib_modules(path.as_path()) {
                                paths.push(prefix.join(entry));
                            }
                        } else if path.is_file() {
                            let file_name = path.file_stem().unwrap();

                            // Special case, don't add prelude to the module list since we don't want to allow
                            // it to be imported under the normal standard library imports.
                            if file_name == PRELUDE {
                                continue;
                            }

                            // This shouldn't happen but if there is a file which does not have a hash extension, we shouldn't add it
                            if path.extension().unwrap_or_default() != "hash" {
                                continue;
                            }

                            paths.push(PathBuf::from(file_name));
                        }
                    }
                    Err(e) => panic!("Unable to read standard library folder: {}", e),
                }
            }
        }

        paths
    }

    pub fn resolve_path(
        &self,
        path: impl AsRef<Path>,
        wd: impl AsRef<Path>,
        location: Location,
    ) -> Result<PathBuf, ParseError> {
        let path = path.as_ref();
        let wd = wd.as_ref();

        let stdlib_path: PathBuf = [BUILD_DIR, "..", "stdlib"].iter().collect();
        let modules = self.get_stdlib_modules(stdlib_path);

        // check if the given path is equal to any of the standard library paths
        if modules.contains(&path.to_path_buf()) {
            return Ok(path.to_path_buf());
        }

        // otherwise, we have to resolve the module path based on the working directory
        let work_dir = wd.canonicalize().unwrap();
        let raw_path = work_dir.join(path);

        // check if that path exists, if not it does return it as an error
        if !raw_path.exists() {
            // @@Copied
            return Err(ParseError::ImportError {
                import_name: path.to_path_buf(),
                location,
            });
        }

        // If the provided path is a directory, we assume that the user is referencing an index
        // module that is located within the given directory. This takes precendence over checking
        // if a module is named that directory.
        // More info on this topic: https://hash-org.github.io/lang/modules.html#importing
        if raw_path.is_dir() {
            let idx_path = raw_path.join("index.hash");

            if idx_path.exists() {
                return Ok(idx_path);
            }

            // ok now check if the user is referencing a module instead of the dir
            let raw_path_hash = raw_path.with_extension("hash");
            if raw_path_hash.exists() {
                return Ok(raw_path_hash);
            }

            // @@Copied
            Err(ParseError::ImportError {
                import_name: path.to_path_buf(),
                location,
            })
        } else {
            // we don't need to anything if the given raw_path already has a extension '.hash',
            // since we don't dissalow someone to import a module and reference the module with
            // the name, like so...
            //
            // > let lib = import("lib.hash");
            // same as...
            // > let lib = import("lib");

            match raw_path.extension() {
                Some(k) if k == "hash" => Ok(raw_path),
                _ => {
                    // add hash extension regardless and check if the path exists...
                    let raw_path_hash = raw_path.with_extension("hash");

                    // Only try to check this route if the provided file did not already have an extension
                    if raw_path.extension().is_none() && raw_path_hash.exists() {
                        Ok(raw_path_hash)
                    } else {
                        Err(ParseError::ImportError {
                            import_name: path.to_path_buf(),
                            location,
                        })
                    }
                }
            }
        }
    }
}
