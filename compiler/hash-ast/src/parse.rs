//! Hash compiler module for parsing source code into AST
//!
//! All rights reserved 2021 (c) The Hash Language authors

use crate::{
    ast::{self, *},
    error::{ParseError, ParseResult},
    module::{ModuleBuilder, Modules, ModuleIdx},
    resolve::{ModuleParsingContext, ModuleResolver, ParModuleResolver},
};
use derive_more::Constructor;
use std::{collections::VecDeque, path::PathBuf, sync::Mutex};
use std::{num::NonZeroUsize, path::Path};

/// A trait for types which can parse a source file into an AST tree.
pub trait Parser<'c> {
    /// Parse a source file with the given `filename` in the given `directory`.
    fn parse(
        &self,
        filename: impl AsRef<Path>,
        directory: impl AsRef<Path>,
    ) -> (Result<(), Vec<ParseError>>, Modules<'c>);

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
    ) -> (
        Result<AstNode<'c, BodyBlock<'c>>, Vec<ParseError>>,
        Modules<'c>,
    );
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
    /// Number of workers the parser should use to parse a job.
    worker_count: NonZeroUsize,
    /// Whether or not to visualise the generated AST
    visualise: bool,
    /// What backend to use for parsing, whether PEST or self hosted.
    backend: B,
}

impl<'c, B> ParParser<B>
where
    B: ParserBackend<'c>,
{
    pub fn new(backend: B, visualise: bool) -> Self {
        Self::new_with_workers(
            backend,
            NonZeroUsize::new(num_cpus::get()).unwrap(),
            visualise,
        )
    }

    pub fn new_with_workers(backend: B, worker_count: NonZeroUsize, visualise: bool) -> Self {
        Self {
            worker_count,
            backend,
            visualise,
        }
    }

    pub fn set_visualisation(&mut self, visualise: bool) {
        self.visualise = visualise;
    }

    fn parse_main(
        &self,
        entry: EntryPoint,
        directory: &Path,
    ) -> (
        Result<Option<AstNode<'c, BodyBlock<'c>>>, Vec<ParseError>>,
        Modules<'c>,
    ) {
        // Spawn thread pool to delegate jobs to. This delegation can occur by acquiring a copy of
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

                    // @@Cleanup: we need to insert the contents of interactive into the module builder...
                    //            At the moment, this isn't the cleanest way of going about the problem, we're
                    //            overwriting the previous content of the interactive session with the current 
                    //            input. This is incorrect because we want to preserve the lines of interactive
                    //            that are considered to be valid (this is a much deeper problem actually.)
                    //
                    //            So, in @@Future, we shouldn't even insert the contents here since it needs
                    //            to pass the typechecking stage and then be inserted into the line, I guess typechecking
                    //            can *evict* the current source line if it is invalid?
                    //
                    //            @@Copying: we're also having to copy the source because we get a &str instead of a String.
                    let copy = interactive_source.to_string();
                    module_builder.add_contents(ModuleIdx(0), PathBuf::from("<interactive>"), copy);

                    // Return the interactive node for interactive entry point.
                    Ok(Some(
                        self.backend
                            .parse_interactive(entry_resolver, interactive_source)?,
                    ))
                }
            }
        });

        let mut errors = errors.into_inner().unwrap();

        // we always need to return modules since they are used for reporting
        let modules = module_builder.build();

        // return the error with any other potential errors that are collected from the interactive
        // statements
        match maybe_interactive_node {
            Err(e) => {
                errors.push_back(e);

                (Err(Vec::from(errors)), modules)
            }
            Ok(block) => {
                if !errors.is_empty() {
                    return (Err(Vec::from(errors)), modules);
                }

                (Ok(block), modules)
            }
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
    ) -> (Result<(), Vec<ParseError>>, Modules<'c>) {
        let filename = filename.as_ref();
        let directory = directory.as_ref();
        let entry = EntryPoint::Module { filename };
        let (state, modules) = self.parse_main(entry, directory);


        // check if the parser returned an error whilst parsing, if so
        // extract the errors and pass them upwards
        if state.is_err() {
            return (Err(state.unwrap_err()), modules);
        }


        // If we need to visualise the file... then do so after the parser has finished
        // the whole tree.
        if self.visualise {
            for module in modules.iter() {
                println!(
                    "file \"{}\":\n{}",
                    module.filename().display(),
                    module.ast()
                );
            }
        }

        (Ok(()), modules)
    }

    fn parse_interactive(
        &self,
        contents: &str,
        directory: impl AsRef<Path>,
    ) -> (
        Result<AstNode<'c, BodyBlock<'c>>, Vec<ParseError>>,
        Modules<'c>,
    ) {
        let directory = directory.as_ref();
        let entry = EntryPoint::Interactive { contents };
        let (result, modules) = self.parse_main(entry, directory);
    
    
        // Ensure that this method always returns a body block or an 
        // error since it can never be `None`.
        match result {
            Ok(Some(block)) => (Ok(block), modules),
            Ok(None) => unreachable!(),
            Err(errors) => (Err(errors), modules)
        }
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
