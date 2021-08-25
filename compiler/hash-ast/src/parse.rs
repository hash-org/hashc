//! Hash compiler module for parsing source code into AST
//!
//! All rights reserved 2021 (c) The Hash Language authors

use crate::{
    ast::{self, *},
    error::{ParseError, ParseResult},
    module::{ModuleBuilder, Modules},
    resolve::{ModuleParsingContext, ModuleResolver, ParModuleResolver},
};
use derive_more::Constructor;
use std::{collections::VecDeque, sync::Mutex};
use std::{num::NonZeroUsize, path::Path};

/// A trait for types which can parse a source file into an AST tree.
pub trait Parser<'c> {
    /// Parse a source file with the given `filename` in the given `directory`.
    fn parse(
        &self,
        filename: impl AsRef<Path>,
        directory: impl AsRef<Path>,
    ) -> ParseResult<Modules<'c>>;

    /// Parse an interactive input string.
    ///
    /// # Arguments
    ///
    /// - `directory`: Input content
    /// - `contents`: Current working directory
    fn parse_interactive(
        &self,
        contents: &str,
        directory: impl AsRef<Path>,
    ) -> ParseResult<(AstNode<'c, BodyBlock<'c>>, Modules<'c>)>;
}

#[derive(Debug, Constructor, Copy, Clone)]
pub(crate) struct ParseErrorHandler<'errors> {
    errors: &'errors Mutex<VecDeque<ParseError>>,
}

impl ParseErrorHandler<'_> {
    pub(crate) fn add_error(&self, error: ParseError) {
        let mut errors = self.errors.lock().unwrap();
        errors.push_back(error);
    }

    pub(crate) fn handle_error<R>(&self, op: impl FnOnce() -> Result<R, ParseError>) -> Option<R> {
        match op() {
            Ok(res) => Some(res),
            Err(err) => {
                self.add_error(err);
                None
            }
        }
    }
}

#[derive(Debug, Constructor)]
pub(crate) struct ParsingContext<'c, 'ctx, B> {
    pub(crate) module_builder: &'ctx ModuleBuilder<'c>,
    pub(crate) backend: &'ctx B,
    pub(crate) error_handler: ParseErrorHandler<'ctx>,
}

impl<'c, 'ctx, B> Clone for ParsingContext<'c, 'ctx, B> {
    fn clone(&self) -> Self {
        Self { ..*self }
    }
}
impl<'c, 'ctx, B> Copy for ParsingContext<'c, 'ctx, B> {}

#[derive(Debug, Copy, Clone)]
enum EntryPoint<'a> {
    Interactive { contents: &'a str },
    Module { filename: &'a Path },
}

pub struct ParParser<B> {
    worker_count: NonZeroUsize,
    backend: B,
}

impl<'c, B> ParParser<B>
where
    B: ParserBackend<'c>,
{
    pub fn new(backend: B) -> Self {
        Self::new_with_workers(backend, NonZeroUsize::new(num_cpus::get()).unwrap())
    }

    pub fn new_with_workers(backend: B, worker_count: NonZeroUsize) -> Self {
        Self {
            worker_count,
            backend,
        }
    }

    fn parse_main(
        &self,
        entry: EntryPoint,
        directory: &Path,
    ) -> ParseResult<(Option<AstNode<'c, BodyBlock<'c>>>, Modules<'c>)> {
        // Spawn threadpool to delegate jobs to. This delegation can occur by acquiring a copy of
        // the `scope` parameter in the pool.scope call below.
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(self.worker_count.get() + 1)
            .thread_name(|id| format!("parse-worker-{}", id))
            .build()
            .unwrap();

        // Data structure used to keep track of all the parsed modules.
        let module_builder = ModuleBuilder::<'c>::new();

        // Store parsing errors in this vector. It is behind a mutex because it needs to be
        // accessed by the pool threads.
        let errors: Mutex<VecDeque<ParseError>> = Default::default();

        // This is the handle used by the pool threads to communicate an error.
        let error_handler = ParseErrorHandler::new(&errors);

        // Create a parsing context from the existing variables.
        let ctx = ParsingContext::new(&module_builder, &self.backend, error_handler);

        let maybe_interactive_node = pool.scope(|scope| -> ParseResult<_> {
            // Here we parse the entry point module that has been given through the function
            // parameters. A copy of `scope` gets passed into the module resolver, which allows it
            // to spawn jobs of its own (notably, when encountering an import).
            //
            // @@Future: we could use the parallelisation capabilities provided by ParModuleResolver to
            // make more aspects of the parser concurrent.

            // The entry point root directory is the one given as argument to this function.
            let entry_root_dir = directory;

            // Determine whether the entry point is a module or interactive input.
            match entry {
                EntryPoint::Module { filename } => {
                    // The entry point has no parent module, or parent source.
                    let entry_parent_index = None;
                    let entry_parent_source = None;

                    // Create a module context and resolver for the entry point.
                    let entry_module_ctx = ModuleParsingContext::new(
                        entry_parent_source,
                        entry_root_dir,
                        entry_parent_index,
                    );
                    let entry_resolver = ParModuleResolver::new(ctx, entry_module_ctx, scope);

                    // No location for the first import
                    let entry_import_location = None;

                    match entry_resolver.add_module(filename, entry_import_location) {
                        Ok(index) => {
                            // On success, mark the module as entry point.
                            module_builder.set_entry_point(index);
                        }
                        Err(err) => {
                            error_handler.add_error(err);
                        }
                    }

                    // No interactive node for a module entry point
                    Ok(None)
                }
                EntryPoint::Interactive {
                    contents: interactive_source,
                } => {
                    // The entry point has no parent module
                    let entry_parent_index = None;

                    // Create a module context and resolver for the entry point.
                    let entry_module_ctx = ModuleParsingContext::new(
                        Some(interactive_source),
                        entry_root_dir,
                        entry_parent_index,
                    );
                    let entry_resolver = ParModuleResolver::new(ctx, entry_module_ctx, scope);

                    // Return the interactive node for interactive entry point.
                    Ok(Some(
                        self.backend
                            .parse_interactive(entry_resolver, interactive_source)?,
                    ))
                }
            }
        })?;

        let mut errors = errors.into_inner().unwrap();
        if let Some(err) = errors.pop_front() {
            Err(err)
        } else {
            // @@Todo: return all errors.
            let modules = module_builder.build();
            Ok((maybe_interactive_node, modules))
        }
    }
}

impl<'c, B> Parser<'c> for ParParser<B>
where
    B: ParserBackend<'c>,
{
    fn parse(
        &self,
        filename: impl AsRef<Path>,
        directory: impl AsRef<Path>,
    ) -> ParseResult<Modules<'c>> {
        let filename = filename.as_ref();
        let directory = directory.as_ref();
        let entry = EntryPoint::Module { filename };
        let (_, modules) = self.parse_main(entry, directory)?;
        Ok(modules)
    }

    fn parse_interactive(
        &self,
        contents: &str,
        directory: impl AsRef<Path>,
    ) -> ParseResult<(AstNode<'c, BodyBlock<'c>>, Modules<'c>)> {
        let directory = directory.as_ref();
        let entry = EntryPoint::Interactive { contents };
        let (interactive, modules) = self.parse_main(entry, directory)?;
        Ok((interactive.unwrap(), modules))
    }
}

pub trait ParserBackend<'c>: Sync + Sized {
    fn parse_module(
        &self,
        resolver: impl ModuleResolver,
        path: &Path,
        contents: &str,
    ) -> ParseResult<ast::Module<'c>>;

    fn parse_interactive(
        &self,
        resolver: impl ModuleResolver,
        contents: &str,
    ) -> ParseResult<AstNode<'c, ast::BodyBlock<'c>>>;
}
