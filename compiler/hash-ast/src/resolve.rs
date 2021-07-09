use std::fs;
use std::path::{Path, PathBuf};

use crossbeam_channel::Sender;
use hash_utils::timed;
use log::{debug, Level};
use crate::module::ModuleIdx;

use crate::{
    error::{ParseError, ParseResult},
    location::SourceLocation,
    parse::{ParMessage, ParserBackend},
};

pub struct ModuleResolver {
    sender: Sender<ParMessage>,
    parent: Option<ModuleIdx>,
    root_dir: PathBuf,
    source: String,
}

impl ModuleResolver {
    pub fn new(
        sender: Sender<ParMessage>,
        source: String,
        parent: Option<ModuleIdx>,
        root_dir: PathBuf,
    ) -> Self {
        Self {
            sender,
            parent,
            root_dir,
            source,
        }
    }

    pub fn get_module_contents(&self) -> &str {
        &self.source
    }

    pub fn add_module(
        &mut self,
        import_path: impl AsRef<Path>,
        location: Option<SourceLocation>,
    ) -> ParseResult<ModuleIdx> {
        let resolved_path = resolve_path(import_path, &self.root_dir, location)?;
        let index = ModuleIdx::new();

        self.sender
            .try_send(ParMessage::ModuleImport {
                index,
                filename: resolved_path,
                parent: self.parent,
            })
            .unwrap();

        Ok(index)
    }

    pub fn add_module_send_error(
        &mut self,
        import_path: impl AsRef<Path>,
        location: Option<SourceLocation>,
    ) -> Option<ModuleIdx> {
        match self.add_module(import_path, location) {
            Ok(index) => Some(index),
            Err(err) => {
                self.sender.try_send(ParMessage::Error(err)).unwrap();
                None
            }
        }
    }

    pub fn parse_file(&mut self, resolved_filename: impl AsRef<Path>, backend: &impl ParserBackend) {
        debug!("Parsing file: {:?}", resolved_filename.as_ref());

        let module = timed(
            || backend.parse_module(self, resolved_filename.as_ref()),
            Level::Debug,
            |elapsed| debug!("ast: {:.2?}", elapsed),
        );

        if let Err(e) = module {
            return self
                .sender
                .try_send(ParMessage::Error(ParseError::from(e)))
                .unwrap();
        }

        let module = module.unwrap();

        self.sender
            .try_send(ParMessage::ParsedModule {
                node: module,
                contents: self.source.to_owned(),
                filename: resolved_filename.as_ref().to_owned(),
            })
            .unwrap();
    }
}

/// The location of a build directory of this package, this used to resolve where the standard library
/// is located at.
static BUILD_DIR: &str = env!("CARGO_MANIFEST_DIR");

/// Name of the prelude module
static PRELUDE: &str = "prelude";

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
    path: impl AsRef<Path>,
    wd: impl AsRef<Path>,
    location: Option<SourceLocation>,
) -> ParseResult<PathBuf> {
    let path = path.as_ref();
    let wd = wd.as_ref();

    let stdlib_path: PathBuf = [BUILD_DIR, "..", "stdlib"].iter().collect();
    let modules = get_stdlib_modules(stdlib_path);

    // check if the given path is equal to any of the standard library paths
    if modules.contains(&path.to_path_buf()) {
        return Ok(path.to_path_buf());
    }

    // otherwise, we have to resolve the module path based on the working directory
    let work_dir = wd.canonicalize().unwrap();
    let raw_path = work_dir.join(path);

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
            src: location.unwrap_or_else(SourceLocation::interactive),
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
                        src: location.unwrap_or_else(SourceLocation::interactive),
                    })
                }
            }
        }
    }
}
