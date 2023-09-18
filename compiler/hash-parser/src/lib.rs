//! Self hosted hash parser, this function contains the implementations for
//! `hash-ast` which provides a general interface to write a parser.
#![feature(cell_update, let_chains)]

mod diagnostics;
mod import_resolver;
pub mod parser;
mod source;

use std::env;

use hash_ast::{
    ast::{self, LocalSpanMap, SpanMap},
    node_map::ModuleEntry,
};
use hash_lexer::{Lexer, LexerMetadata};
use hash_pipeline::{
    fs::read_in_path,
    interface::{CompilerInterface, CompilerStage},
    settings::CompilerStageKind,
    workspace::Workspace,
};
use hash_reporting::{diagnostic::DiagnosticsMut, report::Report, reporter::Reports};
use hash_source::{
    constant::string_table, location::SpannedSource, InteractiveId, ModuleId, SourceId,
    SourceMapUtils,
};
use hash_utils::{
    crossbeam_channel::{unbounded, Sender},
    rayon,
    timing::{HasMutMetrics, StageMetrics},
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
    metrics: StageMetrics,
}

impl Parser {
    /// Merge an incoming set of metrics into the current metrics.
    pub fn merge_metrics(&mut self, metrics: StageMetrics) {
        // @@Improvement: we could record more "precise" metrics about how long
        // it took to lex/parse each module instead of grouping everything together.
        //
        // However, this might make the metrics output more difficult to read, so
        // perhaps there should be a "light" metrics mode, and a more verbose
        // one.
        for metric in metrics.iter() {
            *self.metrics.timings.entry(metric.0).or_default() += metric.1;
        }
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

        // Parse the entry point
        parse_source(ParseSource::from_source(entry_point, Some(current_dir)), sender);

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

                        let path = SourceMapUtils::map(id, |source| source.path().to_path_buf());
                        node_map.add_module(ModuleEntry::new(path, node));
                    }
                    ParserAction::MergeSpans { spans } => scope.spawn(move |_| {
                        SpanMap::add_local_map(spans);
                    }),
                    ParserAction::ParseImport { source, sender } => {
                        // ##Note: import de-duplication is already ensured by the
                        // sender. The resolved path of the specified module is looked
                        // up in the source map before sending this message. If an existing
                        // `SourceId` is already present, then the message is not sent.

                        scope.spawn(move |_| {
                            // reserve a module id for the module we are about to parse.
                            parse_source(ParseSource::from_source(source, None), sender)
                        });
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

    fn metrics(&self) -> StageMetrics {
        self.metrics.clone()
    }

    /// Return the [CompilerStageKind] of the parser.
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Parse
    }
}

/// Messages that are passed from parser workers into the general message queue.
pub enum ParserAction {
    /// A worker has specified that a module should be put in the queue for
    /// lexing and parsing.
    ParseImport { source: SourceId, sender: Sender<ParserAction> },

    /// A unrecoverable error occurred during the parsing or lexing of a module.
    Error { diagnostics: Vec<Report>, timings: StageMetrics },

    /// Update the global `SPAN_MAP` with the specified local span map.
    MergeSpans { spans: LocalSpanMap },

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
        timings: StageMetrics,
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
        timings: StageMetrics,
    },
}

/// Parse a specific source specified by [ParseSource].
fn parse_source(source: ParseSource, sender: Sender<ParserAction>) {
    let mut timings = StageMetrics::default();
    let id = source.id();

    // Read in the contents from disk if this is a module, otherwise copy
    // from the already inserted interactive line.
    let contents = timings.time_item("read", |_| {
        if id.is_interactive() {
            // @@Dumbness: We have to copy out the contents of the interactive line.
            Ok(SourceMapUtils::map(id, |source| source.owned_contents()))
        } else {
            let path = SourceMapUtils::map(id, |source| source.path().to_path_buf());
            read_in_path(path.as_path())
        }
    });

    let Ok(contents) = contents else {
        // We failed to read in the contents of the path, we emit a
        // an error to the diagnostics channel.
        sender
            .send(ParserAction::Error { diagnostics: vec![contents.unwrap_err().into()], timings })
            .unwrap();
        return;
    };

    // @@Debugging: when we want to look at spans produced by the parser, uncomment
    // this line.
    // SourceMapUtils::set_module_source(id, contents.clone());

    let spanned = SpannedSource::from_string(contents.as_str());

    // Lex the contents of the module or interactive block
    let LexerMetadata { tokens, mut diagnostics, strings } =
        timings.time_item("tokenise", |_| Lexer::new(spanned, id).tokenise());

    // Check if the lexer has errors...
    if diagnostics.has_errors() {
        sender
            .send(ParserAction::Error { diagnostics: diagnostics.into_reports(), timings })
            .unwrap();

        // We need to finally put the sources into the source map.
        if id.is_module() {
            SourceMapUtils::set_module_source(id, contents);
        }

        return;
    }

    // if !source.id().is_prelude() {
    //     SourceMapUtils::set_module_source(id, contents.clone());
    //     for token in &tokens {
    //         println!("{:?}, {}, {:?}", token.kind, token.span,
    // Span::new(token.span, id).fmt_range());     }
    // }

    // Update the global string table now!
    string_table().add_local_table(strings);

    // Create a new import resolver in the event of more modules that
    // are encountered whilst parsing this module.
    let resolver = ImportResolver::new(id, source.parent(), sender);
    let mut diagnostics = ParserDiagnostics::new();
    let mut spans = LocalSpanMap::with_capacity(id, tokens.len() * 2);
    let mut gen = AstGen::new(spanned, &tokens, &resolver, &mut diagnostics, &mut spans);

    // Perform the parsing operation now... and send the result through the
    // message queue, regardless of it being an error or not.
    let action = match id.is_interactive() {
        false => {
            let node = timings.time_item("gen", |_| gen.parse_module());
            SourceMapUtils::set_module_source(id, contents);

            ParserAction::SetModuleNode {
                id: id.into(),
                node,
                diagnostics: diagnostics.into_reports(Reports::from, Reports::from),
                timings,
            }
        }
        true => {
            let node = timings.time_item("gen", |_| gen.parse_expr_from_interactive());

            ParserAction::SetInteractiveNode {
                id: id.into(),
                node,
                diagnostics: diagnostics.into_reports(Reports::from, Reports::from),
                timings,
            }
        }
    };

    let sender = resolver.into_sender();

    // Send both the generated module, and the `LocalSpanMap` for updating
    // the global `SPAN_MAP`.
    sender.send(ParserAction::MergeSpans { spans }).unwrap();

    sender.send(action).unwrap();
}
