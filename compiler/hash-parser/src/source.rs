//! Self hosted hash parser, this function contains the implementations for
//! `hash-ast` which provides a general interface to write a parser.

use std::path::PathBuf;

use hash_source::{SourceId, SourceMapUtils};

/// A [ParseSource] represents the pre-processed information before a module
/// or an interactive block gets lexed and parsed.
pub struct ParseSource {
    /// The absolute path for the parent directory of the source, `current_dir`
    /// if it is an interactive block. This is used to resolve other module
    /// that are specified relative to the current [ParseSource] module or
    /// interactive block.
    parent: PathBuf,

    /// The [SourceId] of the source, could be a module or interactive.
    id: SourceId,
}

impl ParseSource {
    /// Create a [ParseSource] from a general [SourceId]
    pub fn from_source(id: SourceId, current_dir: Option<PathBuf>) -> Self {
        if id.is_interactive() {
            Self { id, parent: current_dir.unwrap() }
        } else {
            Self {
                id,
                parent: SourceMapUtils::map(id, |source| {
                    source.path().parent().unwrap().to_owned()
                }),
            }
        }
    }

    /// Get the associated [SourceId] from the [ParseSource]
    pub fn id(&self) -> SourceId {
        self.id
    }

    /// Get the `associated_path` with the [ParseSource]
    pub fn parent(&self) -> &PathBuf {
        &self.parent
    }
}
