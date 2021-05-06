//! Path resolving utilities
//!
//! All rights reserved 2021 (c) The Hash Language authors

// Module names that are  used within the standard library
// const MODULES: &[&Path] = get_stdlib_modules!("./stdlib");
use std::{
    fs,
    path::{Path, PathBuf},
};

static BUILD_DIR: &str = env!("CARGO_MANIFEST_DIR");

/// Function that builds a module map of the standard library that is shipped
/// with the compiler distribution. Standard library modules are referenced
/// within imports 
pub fn get_stdlib_modules(dir: impl AsRef<Path>) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = Vec::new();

    if dir.as_ref().is_dir() {
        for entry in fs::read_dir(dir).unwrap() {
            match entry {
                Ok(p) => {
                    let path = p.path();

                    if path.is_dir() {
                        // recurse and get all of the files with the prefix
                        let prefix: &Path = path.file_stem().unwrap().as_ref();

                        for entry in get_stdlib_modules(path.as_path()) {
                            paths.push(prefix.join(entry));
                        }
                    } else if path.is_file() {
                        let file_name = path.file_stem().unwrap();

                        // Special case, don't add prelude to the module list since we don't want to allow 
                        // it to be imported under the normal standard library imports.
                        if file_name == "prelude" { continue }

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

pub fn resolve_path(_path: &Path) {
    let stdlib_path = Path::new(BUILD_DIR).join("..").join("stdlib");
    let modules = get_stdlib_modules(stdlib_path.as_path());

    println!("{:?}", modules);
}
