//! Module-related containers and utilities.
//
// All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use std::{
    fs,
    path::{Path, PathBuf},
};

use crate::{error::ParseError, location::Location};

/// A module identifier which is an index into [Modules].
pub type ModuleIdx = usize;

// FIXME: this is what we should be looking at rather than doing at runtime!
// Module names that are used within the standard library
// const MODULES: &[&Path] = get_stdlib_modules!("./stdlib");

/// The location of a build directory of this package, this used to resolve where the standard library
/// is located at.
static BUILD_DIR: &str = env!("CARGO_MANIFEST_DIR");

/// Represents a single module.
pub struct Module<'a> {
    idx: usize,
    modules: &'a Modules,
}

impl Module<'_> {
    /// Get the content (source text) of the module.
    pub fn content(&self) -> &str {
        self.modules.contents[self.idx].as_ref()
    }

    /// Get the filename (full path) of the module.
    pub fn filename(&self) -> &str {
        self.modules.filenames[self.idx].as_ref()
    }
}

/// Represents a set of loaded modules.
pub struct Modules {
    filenames: Vec<String>,
    contents: Vec<String>,
}

/// @Incomplete: This will have to change given the fact that we  want to generate this information at compile time.
///              Ideally, we want [`Self::get_stdlib_modules()`] to only generate a vector of pathbufs and the use
///              that to resolve module paths.
impl Modules {
    /// Get the module at the given index.
    pub fn get_module(&self, idx: ModuleIdx) -> Module<'_> {
        Module { idx, modules: self }
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
                            if file_name == "prelude" {
                                continue;
                            }

                            // This shouldn't happen but if there is a file which does not have a hash extension, we shouldn't add it
                            match path.extension() {
                                Some(k) if k == "hash" => paths.push(PathBuf::from(file_name)),
                                _ => {}
                            }
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
        path: &Path,
        wd: &Path,
        location: Location,
    ) -> Result<PathBuf, ParseError> {
        let stdlib_path = Path::new(BUILD_DIR).join("..").join("stdlib");
        let modules = self.get_stdlib_modules(stdlib_path.as_path());

        // check if the given path is equal to any of the standard library paths
        if modules.iter().any(|i| i.clone() == *path) {
            return Ok(path.to_path_buf());
        }

        // otherwise, we have to resolve the module path based on the working directory
        let work_dir = wd.canonicalize().unwrap();
        let mut raw_path = work_dir.join(path);

        // check if that path exists, if not it does return it as an error
        if !raw_path.exists() {
            // @@Copied
            let path = String::from(path.to_str().unwrap());
            return Err(ParseError::ImportError {
                import_name: path,
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
            if raw_path.set_extension("hash") && raw_path.exists() {
                return Ok(raw_path);
            }

            // @@Copied
            let path = String::from(path.to_str().unwrap());
            return Err(ParseError::ImportError {
                import_name: path,
                location,
            });
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
                    // @Correctness: set_extension replaces the previous extension, is this the kind of behaviour we want...
                    if raw_path.set_extension("hash") && raw_path.exists() {
                        Ok(raw_path)
                    } else {
                        // @@Copied
                        let path = String::from(path.to_str().unwrap());
                        Err(ParseError::ImportError {
                            import_name: path,
                            location,
                        })
                    }
                }
            }
        }
    }
}
