//! Self hosted hash parser, this function contains the implementations for
//! `hash-ast` which provides a general interface to write a parser.

use std::path::PathBuf;

use hash_ast::node_map::NodeMap;
use hash_source::{SourceId, SourceMap};

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
    /// Create a new [ParseSource] from a [SourceId].
    pub(crate) fn from_module(id: SourceId, node_map: &NodeMap, source_map: &SourceMap) -> Self {
        let module = node_map.get_module(id.into());
        let contents = source_map.contents(id).to_owned();

        Self { id, contents, path: module.path().parent().unwrap().to_owned() }
    }
    /// Create a new [ParseSource] from a [InteractiveId].
    fn from_interactive(id: SourceId, source_map: &SourceMap, current_dir: PathBuf) -> Self {
        let contents = source_map.contents(id).to_owned();

        Self { id, contents, path: current_dir }
    }

    /// Create a [ParseSource] from a general [SourceId]
    pub fn from_source(
        id: SourceId,
        node_map: &NodeMap,
        source_map: &SourceMap,
        current_dir: PathBuf,
    ) -> Self {
        if id.is_interactive() {
            Self::from_interactive(id, source_map, current_dir)
        } else {
            Self::from_module(id, node_map, source_map)
        }
    }

    /// Get the contents from the [ParseSource]
    pub fn contents(&self) -> &str {
        self.contents.as_str()
    }

    /// Get the associated [SourceId] from the [ParseSource]
    pub fn id(&self) -> SourceId {
        self.id
    }

    /// Get the `associated_path` with the [ParseSource]
    pub fn path(&self) -> &PathBuf {
        &self.path
    }
}
