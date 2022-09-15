//! Self hosted hash parser, this function contains the implementations for
//! `hash-ast` which provides a general interface to write a parser.
use std::path::{Path, PathBuf};

use crossbeam_channel::Sender;
use hash_pipeline::fs::{read_in_path, resolve_path, ImportError};
use hash_source::{constant::InternedStr, SourceId};

use crate::ParserAction;

/// The [ImportResolver] contains internal logic for resolving the path
/// and contents of a module import, in order to prepare it for lexing
/// and parsing.
pub struct ImportResolver<'p> {
    /// The associated [SourceId] with the import resolution.
    source_id: SourceId,
    /// Working directory from where the import path resolution occurs.
    root_dir: &'p Path,
    /// The parser message queue sender.
    sender: Sender<ParserAction>,
}

impl<'p> ImportResolver<'p> {
    /// Create a new [ImportResolver] with a specified [SourceId], working
    /// directory and a message queue sender.
    pub(crate) fn new(
        source_id: SourceId,
        root_dir: &'p Path,
        sender: Sender<ParserAction>,
    ) -> Self {
        Self { root_dir, sender, source_id }
    }

    /// Get the [SourceId] associated with the current [ImportResolver]
    pub(crate) fn current_source_id(&self) -> SourceId {
        self.source_id
    }

    /// Function to perform import resolution. It will attempt to resolve the
    /// contents of the provided `import_path`, resolve the contents of the
    /// module, and then proceed to send a [ParserAction::ParseImport]
    /// through the message queue.
    pub(crate) fn resolve_import(&self, path: InternedStr) -> Result<PathBuf, ImportError> {
        // Read the contents of the file
        let resolved_path = resolve_path(path, self.root_dir)?;
        let contents = read_in_path(resolved_path.as_path())?;

        // Send over the resolved path and the contents of the file
        self.sender
            .send(ParserAction::ParseImport {
                resolved_path: resolved_path.clone(),
                contents,
                sender: self.sender.clone(),
            })
            .unwrap();
        Ok(resolved_path)
    }

    /// Yield a [Sender<ParserAction>] whilst consuming self.
    pub(crate) fn into_sender(self) -> Sender<ParserAction> {
        self.sender
    }
}
