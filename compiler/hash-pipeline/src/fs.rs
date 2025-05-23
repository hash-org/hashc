//! Hash Compiler filesystem utility functions.
use std::{
    env,
    fmt::Display,
    fs, io,
    path::{MAIN_SEPARATOR, Path, PathBuf},
};

use hash_reporting::report::{Report, ReportKind};
use hash_source::constant::StringId;

/// The location of a build directory of this package, this used to resolve
/// where the standard library is located at.
const STDLIB: &str = env!("STDLIB_PATH");

/// The path to the prelude module
pub const PRELUDE: &str =
    const_format::formatcp!("{}{}prelude.hash", env!("STDLIB_PATH"), MAIN_SEPARATOR);

/// Specifies the error kinds of an [ImportError]. Each kind denotes
/// a particular error that can occur when importing a module.
#[derive(Debug, Clone, Copy)]
pub enum ImportErrorKind {
    /// If the file cannot be read by the current session.
    UnreadableFile,

    /// If the path is referencing a directory, but the directory does not
    /// have a `index.hash`.
    MissingIndex,

    /// When the module file is not found in the file system.
    NotFound,
}

impl Display for ImportErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ImportErrorKind::UnreadableFile => write!(f, "unable to read file"),
            ImportErrorKind::MissingIndex => write!(
                f,
                "this directory likely doesn't have a `index.hash` module, consider creating one"
            ),
            ImportErrorKind::NotFound => write!(f, "module not found"),
        }
    }
}

/// Import error is an abstraction to represent errors that are in relevance to
/// IO operations rather than parsing operations.
#[derive(Debug, Clone)]
pub struct ImportError {
    /// The path that was attempted to be imported.
    pub path: StringId,

    /// The kind of error that occurred.
    pub kind: ImportErrorKind,
}

impl Display for ImportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "couldn't import `{}`, {}", self.path.0.to_str(), self.kind)
    }
}

impl From<ImportError> for Report {
    fn from(value: ImportError) -> Self {
        let mut report = Report::new();
        report.kind(ReportKind::Error).title(format!("{value}"));
        report
    }
}

impl From<(PathBuf, io::Error)> for ImportError {
    fn from(value: (PathBuf, io::Error)) -> Self {
        match value.1.kind() {
            io::ErrorKind::NotFound => ImportError {
                path: StringId::new(value.0.to_str().unwrap()),
                kind: ImportErrorKind::NotFound,
            },
            io::ErrorKind::PermissionDenied => ImportError {
                path: StringId::new(value.0.to_str().unwrap()),
                kind: ImportErrorKind::UnreadableFile,
            },
            err => panic!("unexpected IO error occurred during import resolution: {err:?}"),
        }
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
                        if path.as_path().as_os_str() == PRELUDE {
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
                Err(e) => panic!("Unable to read standard library folder: {e}"),
            }
        }
    }

    paths
}

/// Function to read in the contents of a file specified by a [Path]. If
/// reading the file fails, an [ImportError] is returned.
pub fn read_in_path(import_path: impl AsRef<Path>) -> Result<String, ImportError> {
    // Create a interned string to represent the path
    fs::read_to_string(import_path.as_ref()).map_err(|_| ImportError {
        kind: ImportErrorKind::UnreadableFile,
        path: StringId::new(import_path.as_ref().to_str().unwrap()),
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
pub fn resolve_path<'p>(
    path: impl Into<&'p str>,
    wd: impl AsRef<Path>,
) -> Result<PathBuf, ImportError> {
    let path: &str = path.into();
    let import_path = Path::new(&path);
    let wd = wd.as_ref();

    let modules = get_stdlib_modules(STDLIB);

    let canonicalise = |path: &Path| path.canonicalize().map_err(|err| (path.to_path_buf(), err));

    // check if the given path is equal to any of the standard library paths, and
    // if so we prefix it with the standard library path.
    if modules.contains(&import_path.to_path_buf()) {
        let path = Path::new(STDLIB).join(import_path.with_extension("hash"));

        return Ok(canonicalise(&path)?);
    }

    // otherwise, we have to resolve the module path based on the working directory
    let work_dir = canonicalise(wd)?;
    let raw_path = work_dir.join(import_path);

    // If the provided path is a directory, we assume that the user is referencing
    // an index module that is located within the given directory. This takes
    // precedence over checking if a module is named that directory.
    // More info on this topic: https://hash-org.github.io/lang/modules.html#importing
    if raw_path.is_dir() {
        let idx_path = raw_path.join("index.hash");

        if idx_path.exists() {
            return Ok(canonicalise(&idx_path)?);
        }

        // ok now check if the user is referencing a module instead of the dir
        let raw_path_hash = raw_path.with_extension("hash");
        if raw_path_hash.exists() {
            return Ok(canonicalise(&raw_path_hash)?);
        }

        Err(ImportError { path: StringId::new(path), kind: ImportErrorKind::MissingIndex })
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
                    Ok(canonicalise(&raw_path_hash)?)
                } else {
                    Err(ImportError { path: StringId::new(path), kind: ImportErrorKind::NotFound })
                }
            }
        }
    }
}
