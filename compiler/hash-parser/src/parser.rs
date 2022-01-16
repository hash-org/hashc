//! Self hosted hash parser, this function contains the implementations for `hash-ast`
//! which provides a general interface to write a parser.
//!
//! All rights reserved 2021 (c) The Hash Language authors
use crate::error::{ParseError, ParseResult};
use crate::gen::AstGen;
use crate::lexer::Lexer;
use crossbeam_channel::{unbounded, Sender};
use hash_alloc::Castle;
use hash_ast::ast;
use hash_pipeline::fs::{resolve_path, ImportError};
use hash_pipeline::{CompilerResult, Module, Parser, Sources};
use hash_source::location::SourceLocation;
use hash_source::{InteractiveId, ModuleId, SourceId};
use std::borrow::Cow;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub enum ParserAction<'c> {
    Error(ParseError),
    ParseImport {
        resolved_path: PathBuf,
        sender: Sender<ParserAction<'c>>,
    },
    SetInteractiveInfo {
        interactive_id: InteractiveId,
        node: ast::AstNode<'c, ast::BodyBlock<'c>>,
    },
    SetModuleNode {
        module_id: ModuleId,
        node: ast::AstNode<'c, ast::Module<'c>>,
    },
    SetModuleContents {
        module_id: ModuleId,
        contents: String,
    },
}

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

enum ParseSource {
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

impl<'c> ParseSource {
    pub fn from_module(module_id: ModuleId, sources: &Sources<'c>) -> Self {
        let module = sources.get_module(module_id);
        Self::Module {
            module_id,
            resolved_path: module.path().to_owned(),
        }
    }
    pub fn from_interactive(
        interactive_id: InteractiveId,
        sources: &Sources<'c>,
        current_dir: PathBuf,
    ) -> Self {
        let interactive = sources.get_interactive_block(interactive_id);
        Self::Interactive {
            interactive_id,
            interactive_contents: interactive.contents().to_owned(),
            current_dir,
        }
    }

    pub fn from_source(source_id: SourceId, sources: &Sources<'c>, current_dir: PathBuf) -> Self {
        match source_id {
            SourceId::Interactive(interactive_id) => {
                Self::from_interactive(interactive_id, sources, current_dir)
            }
            SourceId::Module(module_id) => Self::from_module(module_id, sources),
        }
    }

    pub fn contents(&self) -> ParseResult<Cow<str>> {
        match self {
            ParseSource::Module { resolved_path, .. } => Ok(Cow::Owned(
                fs::read_to_string(&resolved_path).map_err(|_| {
                    let path = resolved_path.to_string_lossy();
                    ParseError::Import(ImportError {
                        src: None,
                        message: format!("Cannot read file: {}", path),
                        filename: resolved_path.to_owned(),
                    })
                })?,
            )),
            ParseSource::Interactive {
                interactive_contents,
                ..
            } => Ok(Cow::Borrowed(interactive_contents.as_str())),
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

fn parse_source<'c>(source: ParseSource, sender: Sender<ParserAction<'c>>, castle: &'c Castle) {
    let source_id = source.source_id();
    let contents = match source.contents() {
        Ok(source) => source,
        Err(err) => {
            return sender.send(ParserAction::Error(err)).unwrap();
        }
    };

    let current_dir = source.current_dir();

    let wall = castle.wall();
    let mut lexer = Lexer::new(&contents, source_id, &wall);

    // We need to send the source either way
    if let SourceId::Module(module_id) = source_id {
        sender
            .send(ParserAction::SetModuleContents {
                contents: contents.to_string(),
                module_id,
            })
            .unwrap();
    }

    let tokens = match lexer.tokenise() {
        Ok(source) => source,
        Err(err) => {
            return sender.send(ParserAction::Error(err)).unwrap();
        }
    };
    let trees = lexer.into_token_trees();

    let wall = castle.wall();
    let resolver = ImportResolver::new(source_id, current_dir, sender);
    let gen = AstGen::new(&tokens, &trees, &resolver, wall);

    let action = match &source {
        ParseSource::Module { module_id, .. } => match gen.parse_module() {
            Err(err) => ParserAction::Error(err.into()),
            Ok(node) => ParserAction::SetModuleNode {
                module_id: *module_id,
                node,
            },
        },
        ParseSource::Interactive { interactive_id, .. } => {
            match gen.parse_expression_from_interactive() {
                Err(err) => ParserAction::Error(err.into()),
                Ok(node) => ParserAction::SetInteractiveInfo {
                    interactive_id: *interactive_id,
                    node,
                },
            }
        }
    };

    let sender = resolver.into_sender();
    sender.send(action).unwrap();
}

/// Implementation structure for the parser.
pub struct HashParser<'c> {
    castle: &'c Castle,
    pool: rayon::ThreadPool,
}

impl<'c> HashParser<'c> {
    /// Create a new Hash parser with the self hosted backend.
    pub fn new(worker_count: usize, castle: &'c Castle) -> Self {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(worker_count + 1)
            .thread_name(|id| format!("parse-worker-{}", id))
            .build()
            .unwrap();
        Self { pool, castle }
    }

    pub fn parse_main(
        &mut self,
        sources: &mut Sources<'c>,
        entry_point_id: SourceId,
        current_dir: PathBuf,
    ) -> Vec<ParseError> {
        let castle = self.castle;
        let mut errors = Vec::new();
        let (sender, receiver) = unbounded::<ParserAction>();

        // Parse the entry point
        let entry_source_kind = ParseSource::from_source(entry_point_id, sources, current_dir);
        parse_source(entry_source_kind, sender, castle);

        self.pool.scope(|scope| {
            while let Ok(message) = receiver.recv() {
                match message {
                    ParserAction::SetInteractiveInfo {
                        interactive_id,
                        node,
                    } => {
                        sources
                            .get_interactive_block_mut(interactive_id)
                            .set_node(node);
                    }
                    ParserAction::SetModuleContents {
                        module_id,
                        contents,
                    } => {
                        let module = sources.get_module_mut(module_id);
                        module.set_contents(contents);
                    }
                    ParserAction::SetModuleNode { module_id, node } => {
                        let module = sources.get_module_mut(module_id);
                        module.set_node(node);
                    }
                    ParserAction::ParseImport {
                        resolved_path,
                        sender,
                    } => {
                        if sources.get_module_id_by_path(&resolved_path).is_some() {
                            continue;
                        }

                        let module_id = sources.add_module(Module::new(resolved_path.clone()));
                        let source = ParseSource::from_module(module_id, sources);
                        scope.spawn(move |_| parse_source(source, sender, castle));
                    }
                    ParserAction::Error(err) => {
                        errors.push(err);
                    }
                }
            }
        });

        errors
    }
}

impl<'c> Parser<'c> for HashParser<'c> {
    fn parse(&mut self, target: SourceId, sources: &mut Sources<'c>) -> CompilerResult<()> {
        let current_dir = env::current_dir().map_err(ParseError::from)?;
        let errors = self.parse_main(sources, target, current_dir);

        // @@Todo: merge errors
        match errors.into_iter().next() {
            Some(err) => Err(err.into()),
            None => Ok(()),
        }
    }
}
