//! Self hosted hash parser, this function contains the implementations for
//! `hash-ast` which provides a general interface to write a parser.
#![feature(cell_update, is_some_with, let_chains)]

mod diagnostics;
mod import_resolver;
pub mod parser;
mod source;

use std::{env, path::PathBuf};

use crossbeam_channel::{unbounded, Sender};
use hash_ast::ast::{self};
use hash_lexer::Lexer;
use hash_pipeline::{
    sources::{Module, Workspace},
    traits::Parser,
    CompilerResult,
};
use hash_reporting::{diagnostic::Diagnostics, report::Report};
use hash_source::{InteractiveId, ModuleId, ModuleKind, SourceId};
use import_resolver::ImportResolver;
use parser::AstGen;
use source::ParseSource;

/// Messages that are passed from parser workers into the general message queue.
#[derive(Debug)]
pub enum ParserAction {
    /// A worker has specified that a module should be put in the queue for
    /// lexing and parsing.
    ParseImport { resolved_path: PathBuf, contents: String, sender: Sender<ParserAction> },
    /// A unrecoverable error occurred during the parsing or lexing of a module.
    Error(Vec<Report>),
    /// A worker has completed processing an interactive block and now provides
    /// the generated AST.
    SetInteractiveNode {
        /// The corresponding id of the parsed interactive block.
        interactive_id: InteractiveId,
        /// The resultant parsed interactive body block.
        node: ast::AstNode<ast::BodyBlock>,
        /// The parser may still produce diagnostics for this module, and so we
        /// want to propagate this
        diagnostics: Vec<Report>,
    },
    /// A worker has completed processing an module and now provides the
    /// generated AST.
    SetModuleNode {
        /// The corresponding id of the parsed module.
        module_id: ModuleId,
        /// The resultant parsed module.
        node: ast::AstNode<ast::Module>,
        /// The parser may still produce diagnostics for this module, and so we
        /// want to propagate this
        diagnostics: Vec<Report>,
    },
}

/// Parse a specific source specified by [ParseSource].
fn parse_source(source: ParseSource, sender: Sender<ParserAction>) {
    let source_id = source.source_id();
    let contents = source.contents();

    // Lex the contents of the module or interactive block
    let mut lexer = Lexer::new(&contents, source_id);

    let tokens = lexer.tokenise();

    // Check if the lexer has errors...
    if lexer.has_errors() {
        sender.send(ParserAction::Error(lexer.into_reports())).unwrap();
        return;
    }

    let trees = lexer.into_token_trees();

    // Create a new import resolver in the event of more modules that
    // are encountered whilst parsing this module.
    let resolver = ImportResolver::new(source_id, source.path(), sender);

    let mut gen = AstGen::new(&tokens, &trees, &resolver);

    // Perform the parsing operation now... and send the result through the
    // message queue, regardless of it being an error or not.
    let action = match &source.source_id() {
        SourceId::Module(id) => {
            let node = gen.parse_module();

            ParserAction::SetModuleNode { module_id: *id, node, diagnostics: gen.into_reports() }
        }
        SourceId::Interactive(id) => {
            let node = gen.parse_expr_from_interactive();

            ParserAction::SetInteractiveNode {
                interactive_id: *id,
                node,
                diagnostics: gen.into_reports(),
            }
        }
    };

    let sender = resolver.into_sender();
    sender.send(action).unwrap();
}

/// Implementation structure for the parser.
#[derive(Debug, Default)]
pub struct HashParser;

impl<'pool> HashParser {
    /// Create a new [HashParser].
    pub fn new() -> Self {
        Self
    }

    /// Entry point of the parsing job. This will parse the initial entry point
    /// on the main thread to get a map of any dependencies, and then it
    /// will initiate the thread pool message queue. Parser workers add more
    /// `jobs` by sending [ParserAction::ParseImport] messages through the
    /// channel, and other workers set the parsed contents of the modules.
    /// When all message senders go out of scope, the parser finishes executing
    pub fn begin(
        &mut self,
        entry_point_id: SourceId,
        current_dir: PathBuf,
        workspace: &mut Workspace,
        pool: &'pool rayon::ThreadPool,
    ) -> Vec<Report> {
        let mut collected_diagnostics = Vec::new();
        let (sender, receiver) = unbounded::<ParserAction>();

        assert!(pool.current_num_threads() > 1, "Parser loop requires at least 2 workers");

        let node_map = &mut workspace.node_map;
        let source_map = &mut workspace.source_map;

        // Parse the entry point
        let entry_source_kind =
            ParseSource::from_source(entry_point_id, node_map, source_map, current_dir);
        parse_source(entry_source_kind, sender);

        pool.scope(|scope| {
            while let Ok(message) = receiver.recv() {
                match message {
                    ParserAction::SetInteractiveNode { interactive_id, node, diagnostics } => {
                        collected_diagnostics.extend(diagnostics);

                        node_map.get_interactive_block_mut(interactive_id).set_node(node);
                    }
                    ParserAction::SetModuleNode { module_id, node, diagnostics } => {
                        collected_diagnostics.extend(diagnostics);

                        node_map.get_module_mut(module_id).set_node(node);
                    }
                    ParserAction::ParseImport { resolved_path, contents, sender } => {
                        if source_map.get_module_id_by_path(&resolved_path).is_some() {
                            continue;
                        }

                        let module_id = source_map.add_module(
                            resolved_path.clone(),
                            contents,
                            ModuleKind::Normal,
                        );

                        let module = Module::new(resolved_path);
                        node_map.add_module(module_id, module);

                        let source = ParseSource::from_module(module_id, node_map, source_map);
                        scope.spawn(move |_| parse_source(source, sender));
                    }
                    ParserAction::Error(err) => {
                        collected_diagnostics.extend(err);
                    }
                }
            }
        });

        collected_diagnostics
    }
}

impl<'pool> Parser<'pool> for HashParser {
    /// Entry point of the parser. Initialises a job from the specified
    /// `entry_point`, and calls [HashParser::begin].
    fn parse(
        &mut self,
        target: SourceId,
        workspace: &mut Workspace,
        pool: &'pool rayon::ThreadPool,
    ) -> CompilerResult<()> {
        let current_dir = env::current_dir().map_err(|err| vec![err.into()])?;

        let errors = self.begin(target, current_dir, workspace, pool);
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}
