//! Hash compiler module for converting from tokens to an AST tree
//!
//! All rights reserved 2021 (c) The Hash Language authors
use crate::module::ModuleIdx;
use crate::resolve::ModuleResolver;
use crate::{
    ast::{self, *},
    error::{ParseError, ParseResult},
    module::Modules,
};
use closure::closure;
use crossbeam_channel::unbounded;
use log::debug;
use std::sync::atomic::AtomicUsize;
use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::Ordering,
};

#[derive(Debug, Copy, Clone)]
enum EntryPoint<'a> {
    Interactive { contents: &'a str },
    Module { filename: &'a Path },
}

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

pub struct ParParser<B> {
    worker_count: usize,
    backend: B,
}

pub enum ParMessage {
    ModuleImport {
        filename: PathBuf,
        parent: Option<ModuleIdx>,
        index: ModuleIdx,
    },
    ParsedModule {
        node: ast::Module,
        index: ModuleIdx,
    },
    ReadContents {
        filename: PathBuf,
        contents: String,
    },
    Error(ParseError),
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
        let mut modules = Modules::new();
        let senders = AtomicUsize::new(0);

        debug!("Creating worker pool with {} workers", self.worker_count);
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(self.worker_count + 1)
            .build()
            .unwrap();

        let interactive = pool.scope(|scope| -> ParseResult<_> {
            let (s, r) = unbounded::<ParMessage>();

            senders.fetch_add(1, Ordering::SeqCst);

            // if this is interactive mode we essentially have to state the filename is '<interactive>'..
            let contents = match entry {
                EntryPoint::Module { filename } => {
                    fs::read_to_string(filename).map_err(|e| (e, filename.to_owned()))?
                }
                EntryPoint::Interactive { contents } => contents.to_owned(),
            };

            let mut resolver = ModuleResolver::new(s.clone(), contents, None, directory.to_owned());

            let interactive = match entry {
                EntryPoint::Module { filename } => {
                    let entry_index = resolver.add_module_send_error(filename, None);
                    if let Some(entry_index) = entry_index {
                        modules.set_entry_point(entry_index);
                    }
                    None
                }
                EntryPoint::Interactive { contents } => {
                    Some(self.backend.parse_interactive(&mut resolver, contents)?)
                }
            };
            senders.fetch_sub(1, Ordering::SeqCst);

            // start the reciever and listen for any messages from the jobs, continue looping until all of the module
            // dependencies were resovled from the initially supplied file.
            loop {
                match r.try_recv() {
                    Ok(ParMessage::ModuleImport {
                        filename,
                        parent,
                        index,
                    }) => {
                        if let Some(parent) = parent {
                            modules.add_dependency(parent, index);
                        }

                        if !modules.has_path(&filename) {
                            let root_dir = filename.parent().unwrap().to_owned();
                            let s = s.clone();
                            senders.fetch_add(1, Ordering::SeqCst);

                            scope.spawn(closure!(ref senders, |_| {
                                // read the file here and then pass a reference to the resolver with it's file name
                                let contents = fs::read_to_string(filename)
                                    .map_err(|e| (e, filename.to_owned()));

                                match contents {
                                    Ok(contents) => {
                                        s.try_send(ParMessage::ReadContents { filename, contents })
                                            .unwrap();

                                        // let mut resolver = ModuleResolver::new(s, &source, parent, root_dir);

                                        resolver.parse_file(&filename, &self.backend);
                                        senders.fetch_sub(1, Ordering::SeqCst);
                                    }
                                    Err(e) => {
                                        s.try_send(ParMessage::Error(ParseError::from(e))).unwrap();
                                    }
                                }
                            }));
                        } else {
                            continue;
                        }
                    }
                    Ok(ParMessage::ParsedModule { node, index }) => {
                        modules.set_node(index, node);
                    }
                    Ok(ParMessage::ReadContents { filename, contents }) => {
                        modules.add_module(filename, contents);
                    }
                    Ok(ParMessage::Error(e)) => {
                        break Err(e);
                    }
                    Err(_) => {
                        if senders.load(Ordering::SeqCst) == 0 {
                            // All senders disconnected
                            break Ok(interactive);
                        }
                    }
                }
            }
        })?;

        Ok((interactive, modules))
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
    ) -> ParseResult<Module> {
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

pub trait ParserBackend: Sync {
    fn parse_module(&self, resolver: &mut ModuleResolver, path: &Path) -> ParseResult<ast::Module>;

    fn parse_interactive(
        &self,
        resolver: &mut ModuleResolver,
        contents: &str,
    ) -> ParseResult<AstNode<ast::BodyBlock>>;
}
