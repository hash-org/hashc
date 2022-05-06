//! Self hosted hash parser, this function contains the implementations for `hash-ast`
//! which provides a general interface to write a parser.
//!
//! All rights reserved 2022 (c) The Hash Language authors
use std::path::{Path, PathBuf};

use crossbeam_channel::Sender;
use hash_pipeline::fs::{resolve_path, ImportError};
use hash_source::{location::SourceLocation, SourceId};

use crate::ParserAction;

pub struct ImportResolver<'c> {
    source_id: SourceId,
    root_dir: PathBuf,
    sender: Sender<ParserAction<'c>>,
}

impl<'c> ImportResolver<'c> {
    pub fn new(source_id: SourceId, root_dir: PathBuf, sender: Sender<ParserAction<'c>>) -> Self {
        Self {
            root_dir,
            sender,
            source_id,
        }
    }

    pub fn current_source_id(&self) -> SourceId {
        self.source_id
    }

    pub fn parse_import(
        &self,
        import_path: &Path,
        source_location: SourceLocation,
    ) -> Result<PathBuf, ImportError> {
        let resolved_path = resolve_path(import_path, &self.root_dir, Some(source_location))?;
        self.sender
            .send(ParserAction::ParseImport {
                resolved_path: resolved_path.clone(),
                sender: self.sender.clone(),
            })
            .unwrap();
        Ok(resolved_path)
    }

    pub fn into_sender(self) -> Sender<ParserAction<'c>> {
        self.sender
    }
}
