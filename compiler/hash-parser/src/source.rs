//! Self hosted hash parser, this function contains the implementations for
//! `hash-ast` which provides a general interface to write a parser.

use std::{borrow::Cow, path::PathBuf};

use hash_pipeline::sources::NodeMap;
use hash_source::{InteractiveId, ModuleId, SourceId, SourceMap};

/// A [ParseSource] represents the pre-processed information before a module
/// or an interactive block gets lexed and parsed. Logic related to
/// [ParseSource] is used to organise information about the source before like
/// parsing, such as the contents, id and path of the actual source.
pub struct ParseSource {
    /// The absolute path for the current source, `current_dir` if it is an
    /// interactive block.
    path: PathBuf,
    /// The raw contents of the source.
    contents: String,
    /// The [SourceId] of the source
    id: SourceId,
}

impl ParseSource {
    /// Create a new [ParseSource] from a [ModuleId].
    pub fn from_module(module_id: ModuleId, node_map: &NodeMap, source_map: &SourceMap) -> Self {
        let module = node_map.get_module(module_id);
        let contents = source_map.contents_by_id(SourceId::Module(module_id)).to_owned();

        Self {
            id: SourceId::Module(module_id),
            contents,
            path: module.path().parent().unwrap().to_owned(),
        }
    }
    /// Create a new [ParseSource] from a [InteractiveId].
    pub fn from_interactive(
        interactive_id: InteractiveId,
        source_map: &SourceMap,
        current_dir: PathBuf,
    ) -> Self {
        let contents = source_map.contents_by_id(SourceId::Interactive(interactive_id)).to_owned();

        Self { id: SourceId::Interactive(interactive_id), contents, path: current_dir }
    }

    /// Create a [ParseSource] from a general [SourceId]
    pub fn from_source(
        source_id: SourceId,
        node_map: &NodeMap,
        source_map: &SourceMap,
        current_dir: PathBuf,
    ) -> Self {
        match source_id {
            SourceId::Interactive(interactive_id) => {
                Self::from_interactive(interactive_id, source_map, current_dir)
            }
            SourceId::Module(module_id) => Self::from_module(module_id, node_map, source_map),
        }
    }

    /// Get the contents from the [ParseSource]
    pub fn contents(&self) -> Cow<str> {
        Cow::Borrowed(self.contents.as_str())
    }

    /// Get the associated [SourceId] from the [ParseSource]
    pub fn source_id(&self) -> SourceId {
        self.id
    }

    /// Get the `associated_path` with the [ParseSource]
    pub fn path(&self) -> &PathBuf {
        &self.path
    }
}
