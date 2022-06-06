//! Self hosted hash parser, this function contains the implementations for `hash-ast`
//! which provides a general interface to write a parser.
//!
//! All rights reserved 2022 (c) The Hash Language authors
#![feature(cell_update)]
#![feature(is_some_with)]

mod import_resolver;
pub mod parser;
mod source;

use crossbeam_channel::{unbounded, Sender};
use hash_alloc::Castle;
use hash_ast::ast;
use hash_lexer::Lexer;
use hash_pipeline::sources::{Module, Sources};
use hash_pipeline::{CompilerResult, Parser};
use hash_source::{InteractiveId, ModuleId, SourceId};
use import_resolver::ImportResolver;
use parser::{error::ParseError, AstGen};
use source::ParseSource;
use std::env;
use std::path::PathBuf;

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
            return sender.send(ParserAction::Error(err.into())).unwrap();
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
