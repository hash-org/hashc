//! Self hosted hash parser, this function contains the implementations for
//! `hash-ast` which provides a general interface to write a parser.

use std::{borrow::Cow, fs, path::PathBuf};

use hash_pipeline::{fs::ImportError, sources::Sources};
use hash_source::{InteractiveId, ModuleId, SourceId};

use crate::parser::error::ParseError;

pub enum ParseSource {
    Module {
        resolved_path: PathBuf,
        module_id: ModuleId,
    },
    Interactive {
        current_dir: PathBuf,
        interactive_contents: String,
        interactive_id: InteractiveId,
    },
}

impl ParseSource {
    pub fn from_module(module_id: ModuleId, sources: &Sources) -> Self {
        let module = sources.get_module(module_id);
        Self::Module { module_id, resolved_path: module.path().to_owned() }
    }
    pub fn from_interactive(
        interactive_id: InteractiveId,
        sources: &Sources,
        current_dir: PathBuf,
    ) -> Self {
        let interactive = sources.get_interactive_block(interactive_id);
        Self::Interactive {
            interactive_id,
            interactive_contents: interactive.contents().to_owned(),
            current_dir,
        }
    }

    pub fn from_source(source_id: SourceId, sources: &Sources, current_dir: PathBuf) -> Self {
        match source_id {
            SourceId::Interactive(interactive_id) => {
                Self::from_interactive(interactive_id, sources, current_dir)
            }
            SourceId::Module(module_id) => Self::from_module(module_id, sources),
        }
    }

    pub fn contents(&self) -> Result<Cow<str>, ParseError> {
        match self {
            ParseSource::Module { resolved_path, .. } => {
                Ok(Cow::Owned(fs::read_to_string(&resolved_path).map_err(|_| {
                    let path = resolved_path.to_string_lossy();
                    ParseError::Import(ImportError {
                        src: None,
                        message: format!("Cannot read file: {}", path),
                        filename: resolved_path.to_owned(),
                    })
                })?))
            }
            ParseSource::Interactive { interactive_contents, .. } => {
                Ok(Cow::Borrowed(interactive_contents.as_str()))
            }
        }
    }

    pub fn source_id(&self) -> SourceId {
        match self {
            ParseSource::Module { module_id, .. } => SourceId::Module(*module_id),
            ParseSource::Interactive { interactive_id, .. } => {
                SourceId::Interactive(*interactive_id)
            }
        }
    }

    pub fn current_dir(&self) -> PathBuf {
        match self {
            ParseSource::Module { resolved_path, .. } => resolved_path.parent().unwrap().to_owned(),
            ParseSource::Interactive { current_dir, .. } => current_dir.to_owned(),
        }
    }
}
