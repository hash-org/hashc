//! Self hosted hash parser, this function contains the implementations for
//! `hash-ast` which provides a general interface to write a parser.
#![feature(cell_update, is_some_with)]

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
    /// An error occurred during the parsing or lexing of a module.
    Error(Vec<Report>),
    /// A worker has specified that a module should be put in the queue for
    /// lexing and parsing.
    ParseImport { resolved_path: PathBuf, contents: String, sender: Sender<ParserAction> },
    /// A worker has completed processing an interactive block and now provides
    /// the generated AST.
    SetInteractiveNode { interactive_id: InteractiveId, node: ast::AstNode<ast::BodyBlock> },
    /// A worker has completed processing an module and now provides the
    /// generated AST.
    SetModuleNode { module_id: ModuleId, node: ast::AstNode<ast::Module> },
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

    let gen = AstGen::new(&tokens, &trees, &resolver);

    // Perform the parsing operation now... and send the result through the
    // message queue, regardless of it being an error or not.
    let action = match &source.source_id() {
        SourceId::Module(id) => match gen.parse_module() {
            Err(err) => ParserAction::Error(vec![err.into()]),
            Ok(node) => ParserAction::SetModuleNode { module_id: *id, node },
        },
        SourceId::Interactive(id) => match gen.parse_expr_from_interactive() {
            Err(err) => ParserAction::Error(vec![err.into()]),
            Ok(node) => ParserAction::SetInteractiveNode { interactive_id: *id, node },
        },
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
        let mut errors = Vec::new();
        let (sender, receiver) = unbounded::<ParserAction>();

        assert!(pool.current_num_threads() > 1, "Parser loop requires at least 2 workers");

        // Parse the entry point
        let entry_source_kind = ParseSource::from_source(entry_point_id, workspace, current_dir);
        parse_source(entry_source_kind, sender);

        pool.scope(|scope| {
            while let Ok(message) = receiver.recv() {
                match message {
                    ParserAction::SetInteractiveNode { interactive_id, node } => {
                        workspace
                            .node_map_mut()
                            .get_interactive_block_mut(interactive_id)
                            .set_node(node);
                    }
                    ParserAction::SetModuleNode { module_id, node } => {
                        workspace.node_map_mut().get_module_mut(module_id).set_node(node);
                    }
                    ParserAction::ParseImport { resolved_path, contents, sender } => {
                        if workspace.get_module_id_by_path(&resolved_path).is_some() {
                            continue;
                        }

                        let module_id = workspace.add_module(
                            contents,
                            Module::new(resolved_path.clone()),
                            ModuleKind::Normal,
                        );

                        let source = ParseSource::from_module(module_id, workspace);
                        scope.spawn(move |_| parse_source(source, sender));
                    }
                    ParserAction::Error(err) => {
                        errors.extend(err);
                    }
                }
            }
        });

        errors
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
