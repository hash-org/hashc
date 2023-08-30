//! Self hosted hash parser, this function contains the implementations for
//! `hash-ast` which provides a general interface to write a parser.
#![feature(cell_update, let_chains)]

mod diagnostics;
mod import_resolver;
pub mod parser;
mod source;

use std::{env, ops::AddAssign, path::PathBuf, time::Duration};

use hash_ast::{ast, node_map::ModuleEntry};
use hash_lexer::Lexer;
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage, StageMetrics},
    settings::CompilerStageKind,
    workspace::Workspace,
};
use hash_reporting::{
    diagnostic::{AccessToDiagnosticsMut, Diagnostics},
    report::Report,
    reporter::Reports,
};
use hash_source::{InteractiveId, ModuleId, ModuleKind, SourceId};
use hash_utils::{
    crossbeam_channel::{unbounded, Sender},
    indexmap::IndexMap,
    rayon,
    timing::{time_item, AccessToMetrics},
};
use import_resolver::ImportResolver;
use parser::AstGen;
use source::ParseSource;

use crate::diagnostics::ParserDiagnostics;

/// The [Parser] stage is responsible for parsing the source code into an
/// abstract syntax tree (AST). The parser will also perform some basic
/// semantic analysis, such as resolving imports, and some other basic
/// semantic checks (due to them being syntax bound)
#[derive(Debug, Default)]
pub struct Parser {
    /// The metrics for the parser stage.
    metrics: IndexMap<&'static str, Duration>,
}

impl Parser {
    /// Merge an incoming set of metrics into the current metrics.
    pub fn merge_metrics(&mut self, metrics: ParseTimings) {
        // @@Improvement: we could record more "precise" metrics about how long
        // it took to lex/parse each module instead of grouping everything together.
        //
        // However, this might make the metrics output more difficult to read, so
        // perhaps there should be a "light" metrics mode, and a more verbose
        // one.
        self.metrics.entry("tokenise").or_default().add_assign(metrics.tokenise);
        self.metrics.entry("gen").or_default().add_assign(metrics.gen);
    }
}

/// The [ParserCtx] represents all of the required information that the
/// [Parser] stage needs to query from the pipeline.
pub struct ParserCtx<'p> {
    /// Reference to the current compiler workspace.
    pub workspace: &'p mut Workspace,

    /// Reference to the rayon thread pool.
    pub pool: &'p rayon::ThreadPool,
}

pub trait ParserCtxQuery: CompilerInterface {
    fn data(&mut self) -> ParserCtx;
}

impl<Ctx: ParserCtxQuery> CompilerStage<Ctx> for Parser {
    /// Return the [CompilerStageKind] of the parser.
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Parse
    }

    fn metrics(&self) -> StageMetrics {
        StageMetrics {
            timings: self.metrics.iter().map(|(item, time)| (*item, *time)).collect::<Vec<_>>(),
        }
    }

    /// Entry point of the parser. Initialises a job from the specified
    /// `entry_point`.
    fn run(
        &mut self,
        entry_point: SourceId,
        ctx: &mut Ctx,
    ) -> hash_pipeline::interface::CompilerResult<()> {
        let ParserCtx { workspace, pool } = &mut ctx.data();
        let current_dir = env::current_dir().map_err(|err| vec![err.into()])?;

        let mut collected_diagnostics = Vec::new();
        let (sender, receiver) = unbounded::<ParserAction>();

        assert!(pool.current_num_threads() > 1, "Parser loop requires at least 2 workers");

        let node_map = &mut workspace.node_map;
        let source_map = &mut workspace.source_map;

        // Parse the entry point
        let entry_source_kind =
            ParseSource::from_source(entry_point, node_map, source_map, current_dir);
        parse_source(entry_source_kind, sender);

        pool.scope(|scope| {
            while let Ok(message) = receiver.recv() {
                match message {
                    ParserAction::SetInteractiveNode { id, node, diagnostics, timings } => {
                        collected_diagnostics.extend(diagnostics);
                        self.merge_metrics(timings);
                        node_map.get_interactive_block_mut(id).set_node(node);
                    }
                    ParserAction::SetModuleNode { id, node, diagnostics, timings } => {
                        collected_diagnostics.extend(diagnostics);
                        self.merge_metrics(timings);
                        node_map.get_module_mut(id).set_node(node);
                    }
                    ParserAction::ParseImport { resolved_path, contents, sender } => {
                        if source_map.get_id_by_path(&resolved_path).is_some() {
                            continue;
                        }

                        let module_id = source_map.add_module(
                            resolved_path.clone(),
                            contents,
                            ModuleKind::Normal,
                        );

                        let module = ModuleEntry::new(resolved_path);
                        node_map.add_module(module);

                        let source = ParseSource::from_module(module_id, node_map, source_map);
                        scope.spawn(move |_| parse_source(source, sender));
                    }
                    ParserAction::Error { diagnostics, timings } => {
                        collected_diagnostics.extend(diagnostics);
                        self.merge_metrics(timings);
                    }
                }
            }
        });

        if collected_diagnostics.is_empty() {
            Ok(())
        } else {
            Err(collected_diagnostics)
        }
    }

    /// Any other stage than `semantic_pass` is valid when `--dump-ast` is
    /// specified.
    fn cleanup(&mut self, entry_point: SourceId, ctx: &mut Ctx) {
        let settings = ctx.settings();
        let mut stdout = ctx.output_stream();

        if settings.stage < CompilerStageKind::UntypedAnalysis && settings.ast_settings().dump {
            let set = settings.character_set;
            let mode = settings.ast_settings.dump_mode;
            ctx.workspace().print_sources(entry_point, mode, set, &mut stdout).unwrap();
        }
    }
}

/// A collection of timings for the parser stage. The stage records
/// the amount of time it takes to lex and parse a module, or an
/// interactive block. This infomation is later recorded, and can
/// then be grouped together and displayed with other stages.
#[derive(Debug, Clone, Copy, Default)]
pub struct ParseTimings {
    /// The amount of time the lexer took to tokenise the source.
    tokenise: Duration,

    /// The amound of time the parser took to generate AST for the
    /// source.
    gen: Duration,
}

impl AccessToMetrics for ParseTimings {
    fn add_metric(&mut self, name: &'static str, time: Duration) {
        match name {
            "tokenise" => self.tokenise = time,
            "gen" => self.gen = time,
            _ => unreachable!(),
        }
    }
}

/// Messages that are passed from parser workers into the general message queue.
#[derive(Debug)]
pub enum ParserAction {
    /// A worker has specified that a module should be put in the queue for
    /// lexing and parsing.
    ParseImport { resolved_path: PathBuf, contents: String, sender: Sender<ParserAction> },

    /// A unrecoverable error occurred during the parsing or lexing of a module.
    Error { diagnostics: Vec<Report>, timings: ParseTimings },

    /// A worker has completed processing an interactive block and now provides
    /// the generated AST.
    SetInteractiveNode {
        /// The corresponding [InteractiveId] of the parsed interactive block.
        id: InteractiveId,

        /// The resultant parsed interactive body block.
        node: ast::AstNode<ast::BodyBlock>,

        /// The parser may still produce diagnostics for this module, and so we
        /// want to propagate this
        diagnostics: Vec<Report>,

        /// The timings of the parse operation.
        timings: ParseTimings,
    },

    /// A worker has completed processing an module and now provides the
    /// generated AST.
    SetModuleNode {
        /// The corresponding [ModuleId] of the parsed module.
        id: ModuleId,

        /// The resultant parsed module.
        node: ast::AstNode<ast::Module>,

        /// The parser may still produce diagnostics for this module, and so we
        /// want to propagate this
        diagnostics: Vec<Report>,

        /// The timings of the parse operation.
        timings: ParseTimings,
    },
}

/// Parse a specific source specified by [ParseSource].
fn parse_source(source: ParseSource, sender: Sender<ParserAction>) {
    let source_id = source.id();
    let mut timings = ParseTimings::default();

    // Lex the contents of the module or interactive block
    let mut lexer = Lexer::new(source.contents(), source_id);
    let tokens = time_item(&mut timings, "tokenise", |_| lexer.tokenise());

    // Check if the lexer has errors...
    if lexer.has_errors() {
        sender.send(ParserAction::Error { diagnostics: lexer.into_reports(), timings }).unwrap();
        return;
    }

    let trees = lexer.into_token_trees();

    // Create a new import resolver in the event of more modules that
    // are encountered whilst parsing this module.
    let resolver = ImportResolver::new(source_id, source.path(), sender);
    let diagnostics = ParserDiagnostics::new();
    let mut gen = AstGen::new(source.contents(), &tokens, &trees, &resolver, &diagnostics);

    // Perform the parsing operation now... and send the result through the
    // message queue, regardless of it being an error or not.
    let id = source.id();
    let action = match id.is_interactive() {
        false => {
            let node = time_item(&mut timings, "gen", |_| gen.parse_module());
            ParserAction::SetModuleNode {
                id: id.into(),
                node,
                diagnostics: diagnostics.into_reports(Reports::from, Reports::from),
                timings,
            }
        }
        true => {
            let node = time_item(&mut timings, "gen", |_| gen.parse_expr_from_interactive());
            ParserAction::SetInteractiveNode {
                id: id.into(),
                node,
                diagnostics: diagnostics.into_reports(Reports::from, Reports::from),
                timings,
            }
        }
    };

    let sender = resolver.into_sender();
    sender.send(action).unwrap();
}
