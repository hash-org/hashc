//! Hash compiler module for parsing source code into AST
//!
//! All rights reserved 2021 (c) The Hash Language authors

use crate::{
    ast::{self, *},
    error::{ParseError, ParseResult},
    module::{ModuleBuilder, Modules},
    resolve::{ModuleParsingContext, ModuleResolver, ParModuleResolver},
};
use derive_getters::Getters;
use derive_more::Constructor;
use std::path::Path;
use std::sync::Mutex;

pub trait Parser {
    fn parse(
        &self,
        filename: impl AsRef<Path>,
        directory: impl AsRef<Path>,
    ) -> ParseResult<Modules>;

    fn parse_interactive(
        &self,
        contents: &str,
        directory: impl AsRef<Path>,
    ) -> ParseResult<(AstNode<BodyBlock>, Modules)>;
}

#[derive(Debug, Constructor, Copy, Clone)]
pub(crate) struct ParseErrorHandler<'errors> {
    errors: &'errors Mutex<Vec<ParseError>>,
}

impl ParseErrorHandler<'_> {
    pub(crate) fn add_error(&self, error: ParseError) {
        let mut errors = self.errors.lock().unwrap();
        errors.push(error);
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

#[derive(Debug, Constructor, Getters)]
pub(crate) struct ParsingContext<'ctx, B> {
    module_builder: &'ctx ModuleBuilder,
    backend: &'ctx B,
    error_handler: ParseErrorHandler<'ctx>,
}

impl<B> Clone for ParsingContext<'_, B> {
    fn clone(&self) -> Self {
        Self { ..*self }
    }
}
impl<B> Copy for ParsingContext<'_, B> {}

#[derive(Debug, Copy, Clone)]
enum EntryPoint<'a> {
    Interactive { contents: &'a str },
    Module { filename: &'a Path },
}

pub struct ParParser<B> {
    worker_count: usize,
    backend: B,
}

impl<B> ParParser<B>
where
    B: ParserBackend,
{
    pub fn new(backend: B) -> Self {
        Self::new_with_workers(backend, num_cpus::get())
    }

    pub fn new_with_workers(backend: B, worker_count: usize) -> Self {
        if worker_count == 0 {
            panic!("Cannot spawn a parallel parser with 0 threads");
        }

        Self {
            worker_count,
            backend,
        }
    }

    fn parse_main(
        &self,
        entry: EntryPoint,
        directory: &Path,
    ) -> ParseResult<(Option<AstNode<BodyBlock>>, Modules)> {
        let module_builder = ModuleBuilder::new();
        let errors: Mutex<Vec<ParseError>> = Default::default();
        let error_handler = ParseErrorHandler::new(&errors);
        let ctx = ParsingContext::new(&module_builder, &self.backend, error_handler);

        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(self.worker_count + 1)
            .build()
            .unwrap();

        let maybe_interactive_node = pool.scope(|scope| -> ParseResult<_> {
            // The entry point root directory is the one given as argument to this function.
            let entry_root_dir = directory;

            // The entry point has no parent module, or parent source.
            let entry_parent_index = None;
            let entry_parent_source = None;

            // Create a module context and resolver for the entry point.
            let entry_module_ctx =
                ModuleParsingContext::new(entry_parent_source, entry_root_dir, entry_parent_index);
            let mut entry_resolver = ParModuleResolver::new(ctx, entry_module_ctx, scope);

            match entry {
                EntryPoint::Module { filename } => {
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
                EntryPoint::Interactive { contents } => {
                    // Return the interactive node for interactive entry point.
                    Ok(Some(
                        self.backend
                            .parse_interactive(&mut entry_resolver, contents)?,
                    ))
                }
            }
        })?;

        // @@Todo: return errors.
        let modules = module_builder.build();
        Ok((maybe_interactive_node, modules))
    }
}

impl<B> Parser for ParParser<B>
where
    B: ParserBackend,
{
    fn parse(
        &self,
        filename: impl AsRef<Path>,
        directory: impl AsRef<Path>,
    ) -> ParseResult<Modules> {
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
    ) -> ParseResult<(AstNode<BodyBlock>, Modules)> {
        let directory = directory.as_ref();
        let entry = EntryPoint::Interactive { contents };
        let (interactive, modules) = self.parse_main(entry, directory)?;
        Ok((interactive.unwrap(), modules))
    }
}

pub trait ParserBackend: Sync + Sized {
    fn parse_module(
        &self,
        resolver: &mut impl ModuleResolver,
        path: &Path,
        contents: &str,
    ) -> ParseResult<ast::Module>;

    fn parse_interactive(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &str,
    ) -> ParseResult<AstNode<ast::BodyBlock>>;
}
