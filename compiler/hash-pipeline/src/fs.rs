//! Hash Compiler filesystem utility functions.
use std::{
    fs,
    path::{Path, PathBuf},
};

use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_source::location::SourceLocation;
use thiserror::Error;

/// The location of a build directory of this package, this used to resolve
/// where the standard library is located at.
static STDLIB: &str = env!("STDLIB_PATH");

/// Name of the prelude module
pub static PRELUDE: &str = concat!(env!("STDLIB_PATH"), "/", "prelude");

/// Import error is an abstraction to represent errors that are in relevance to
/// IO operations rather than parsing operations.
#[derive(Debug, Clone, Error)]
#[error("couldn't import `{filename}`, {message}")]
pub struct ImportError {
    pub filename: PathBuf,
    pub message: String,
    pub location: Option<SourceLocation>,
}

impl ImportError {
    /// Create a [Report] from the [ImportError].
    pub fn create_report(&self) -> Report {
        let mut builder = ReportBuilder::new();
        builder.with_kind(ReportKind::Error).with_message("Failed to import");

        if let Some(src) = self.location {
            builder
                .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "here")))
                .add_element(ReportElement::Note(ReportNote::new(
                    ReportNoteKind::Note,
                    &self.message,
                )));
        } else {
            builder.with_message(format!("Failed to import: {}", self.message));
        }

        builder.build()
    }
}

/// Function that builds a module map of the standard library that is shipped
/// with the compiler distribution. Standard library modules are referenced
/// within imports
fn get_stdlib_modules(dir: impl AsRef<Path>) -> Vec<PathBuf> {
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

                        // Special case, don't add prelude to the module list since we don't want to
                        // allow it to be imported under the normal standard
                        // library imports.
                        if file_name == PRELUDE {
                            continue;
                        }

                        // This shouldn't happen but if there is a file which does not have a hash
                        // extension, we shouldn't add it
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

/// Function to read in the contents of a file specified by a [Path]. If
/// reading the file fails, an [ImportError] is returned.
pub fn read_in_path(path: &Path) -> Result<String, ImportError> {
    fs::read_to_string(path).map_err(|_| ImportError {
        location: None,
        message: format!("Cannot read file: {}", path.to_string_lossy()),
        filename: path.to_owned(),
    })
}

/// Function used to resolve the path of a module according to the language
/// resolution rules.
///
/// ## Rules
///
/// The function tries to resolve the path according to the following rules
///
/// - If the module specified path is a relative path in the `root` of the
///   standard library, then it's assumed that this is a reference to a file
///   within the standard library. If the specified path has `.hash` extension,
///   this circumvents the assumption.
///
/// - If the specified path has no `.hash` extension, and the path is not a
///   file, but a directory, then it is assumed that the path might be referring
///   to a `index.hash` file within the directory itself. If there is an
///   `index.hash` within the folder, and no file exists with the same name on
///   the directory level, then it is assumed that `index.hash` is the
///   reference.
///
/// - If the file path exists, relative `wd`, then the combined file path is the
///   module path.
///
/// ## Errors
/// - If the path to the module couldn't be resolved, an [ImportError] is
///   raised.
pub fn resolve_path(
    path: impl AsRef<Path>,
    wd: impl AsRef<Path>,
    location: Option<SourceLocation>,
) -> Result<PathBuf, ImportError> {
    let path = path.as_ref();
    let wd = wd.as_ref();

    let modules = get_stdlib_modules(STDLIB);

    // check if the given path is equal to any of the standard library paths
    if modules.contains(&path.to_path_buf()) {
        return Ok(path.to_path_buf());
    }

    // otherwise, we have to resolve the module path based on the working directory
    let work_dir = wd.canonicalize().unwrap();
    let raw_path = work_dir.join(path);

    // If the provided path is a directory, we assume that the user is referencing
    // an index module that is located within the given directory. This takes
    // precedence over checking if a module is named that directory.
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
        Err(ImportError {
            filename: path.to_path_buf(),
            message:
                "This directory likely doesn't have a `index.hash` module, consider creating one."
                    .to_string(),
            location,
        })
    } else {
        // we don't need to anything if the given raw_path already has a extension
        // '.hash', since we don't disallow someone to import a module and
        // reference the module with the name, like so...
        // ```text
        // lib := import("lib.hash");
        // ```
        //
        // same as...
        // ```text
        // lib := import("lib");
        // ```

        match raw_path.extension() {
            Some(k) if k == "hash" => Ok(raw_path),
            _ => {
                // add hash extension regardless and check if the path exists...
                let raw_path_hash = raw_path.with_extension("hash");

                // Only try to check this route if the provided file did not already have an
                // extension
                if raw_path.extension().is_none() && raw_path_hash.exists() {
                    Ok(raw_path_hash)
                } else {
                    Err(ImportError {
                        filename: path.to_path_buf(),
                        message: "module couldn't be found".to_string(),
                        location,
                    })
                }
            }
        }
    }
}
