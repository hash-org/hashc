//! Hash compiler module for converting from tokens to an AST tree
//!
//! All rights reserved 2021 (c) The Hash Language authors
use crate::{
    ast::{self, *},
    error::{ParseError, ParseResult},
    location::SourceLocation,
};
use log::{debug, log_enabled, Level};
use std::iter;
use std::{
    collections::{HashMap, HashSet},
    fs, mem,
    path::{Path, PathBuf},
    sync::atomic::Ordering,
    time::Instant,
};
use std::{sync::atomic::AtomicUsize, time::Duration};

pub struct Parser<'alloc, B, A> {
    worker_count: Option<usize>,
    backend: B,
    allocator: &'alloc A,
}

pub enum ParMessage<'ast> {
    ModuleImport {
        filename: PathBuf,
        parent: Option<ModuleIdx>,
        index: ModuleIdx,
    },
    ParsedModule {
        node: ast::Module<'ast>,
        filename: PathBuf,
        contents: String,
    },
    Error(ParseError),
}

#[derive(Debug, Copy, Clone)]
enum EntryPoint<'a> {
    Interactive { contents: &'a str },
    Module { filename: &'a Path },
}

impl<'ast, 'alloc, B, A> Parser<'alloc, B, A>
where
    B: ParserBackend,
    A: AstAllocator<'ast, 'alloc>,
    'ast: 'alloc,
{
    pub fn sequential(backend: B, allocator: &'alloc A) -> Self {
        Parser {
            worker_count: None,
            backend,
            allocator,
        }
    }

    pub fn parallel(backend: B, allocator: &'alloc A) -> Self {
        Self::parallel_with_workers(backend, allocator, num_cpus::get())
    }

    pub fn parallel_with_workers(backend: B, allocator: &'alloc A, workers: usize) -> Self {
        Parser {
            worker_count: Some(workers),
            backend,
            allocator,
        }
    }

    fn parse_seq(&self, entry: EntryPoint, directory: &Path) -> ParseResult<Modules<'ast>> {
        let mut modules = Modules::new();

        let entry_index = match entry {
            EntryPoint::Module { filename } => {
                let mut resolver = SeqModuleResolver::new(
                    &mut modules,
                    directory.to_owned(),
                    &self.backend,
                    None,
                    self.allocator,
                );
                resolver.add_module(filename, None)?
            }
            EntryPoint::Interactive { contents } => {
                let index = modules.next_index();

                let statement = {
                    let mut resolver = SeqModuleResolver::new(
                        &mut modules,
                        directory.to_owned(),
                        &self.backend,
                        Some(index),
                        self.allocator,
                    );

                    self.backend
                        .parse_statement(&mut resolver, contents, self.allocator)
                }?;

                let module = ast::Module {
                    contents: self.allocator.alloc_ast_nodes(iter::once(statement)),
                };

                modules.add_module("<interactive>".into(), module, contents.to_owned());
                index
            }
        };

        modules.set_entry_point(entry_index);

        Ok(modules)
    }

    fn parse_par(
        &self,
        _entry: EntryPoint,
        _directory: &Path,
        _worker_count: usize,
    ) -> ParseResult<Modules<'ast>> {
        unimplemented!()
        // let mut modules = Modules::new();

        // let module_counter = AtomicUsize::new(0);

        // info!("Creating worker pool with {} workers", worker_count);
        // let pool = rayon::ThreadPoolBuilder::new()
        //     .num_threads(worker_count)
        //     .build()
        //     .unwrap();

        // pool.scope(|scope| -> ParseResult<()> {
        //     let (s, r) = unbounded::<ParMessage>();
        //     let bump = self.herd.get().as_bump();

        //     // spawn the initial job
        //     let mut resolver =
        //         ParModuleResolver::new(s.clone(), &module_counter, None, directory.to_owned());
        //     let entry_index = match entry {
        //         EntryPoint::Module { filename } => resolver.add_module_send_error(filename, None),
        //         EntryPoint::Interactive { contents } => {
        //             let statement =
        //                 self.backend
        //                     .parse_statement(&mut resolver, contents, bump)?;
        //             let module_node = ast::Module {
        //                 contents: bumpalo::vec![in bump; statement],
        //             };
        //             let module = modules.add_module(
        //                 "<interactive>".into(),
        //                 module_node,
        //                 contents.to_owned(),
        //             );

        //             Some(module.index())
        //         }
        //     };
        //     if let Some(entry_index) = entry_index {
        //         modules.set_entry_point(entry_index);
        //     }

        //     // start the reciever and listen for any messages from the jobs, continue looping until all of the module
        //     // dependencies were resovled from the initially supplied file.
        //     loop {
        //         match r.recv() {
        //             Ok(ParMessage::ModuleImport {
        //                 filename,
        //                 parent,
        //                 index,
        //             }) => {
        //                 if let Some(parent) = parent {
        //                     modules.add_dependency(parent, index);
        //                 }

        //                 if !modules.has_path(&filename) {
        //                     let root_dir = filename.parent().unwrap().to_owned();

        //                     // TODO: FIXME
        //                     // scope.spawn(closure!(ref module_counter, ref s, |_| {
        //                     //     let mut resolver = ParModuleResolver::new(
        //                     //         s.clone(),
        //                     //         &module_counter,
        //                     //         parent,
        //                     //         root_dir,
        //                     //     );
        //                     //     resolver.parse_file(filename, &self.backend);
        //                     // }));
        //                 } else {
        //                     continue;
        //                 }
        //             }
        //             Ok(ParMessage::ParsedModule {
        //                 node,
        //                 filename,
        //                 contents,
        //             }) => {
        //                 modules.add_module(filename, node, contents);
        //             }
        //             Ok(ParMessage::Error(e)) => {
        //                 break Err(e);
        //             }
        //             Err(_) => {
        //                 // All senders disconnected
        //                 break Ok(());
        //             }
        //         }
        //     }
        // })?;

        // // Ok to unwrap because no one else has a reference to modules
        // Ok(modules)
    }

    pub fn parse(
        &'ast self,
        filename: impl AsRef<Path>,
        directory: impl AsRef<Path>,
    ) -> ParseResult<Modules<'ast>> {
        let filename = filename.as_ref();
        let directory = directory.as_ref();
        let entry = EntryPoint::Module { filename };

        match self.worker_count {
            None => self.parse_seq(entry, directory),
            Some(worker_count) => self.parse_par(entry, directory, worker_count),
        }
    }

    pub fn parse_statement(
        &'ast self,
        contents: &str,
        directory: impl AsRef<Path>,
    ) -> ParseResult<Modules<'ast>> {
        let directory = directory.as_ref();
        let entry = EntryPoint::Interactive { contents };
        match self.worker_count {
            None => self.parse_seq(entry, directory),
            Some(worker_count) => self.parse_par(entry, directory, worker_count),
        }
    }
}

/// A module identifier which is an index into [Modules].
#[derive(Eq, PartialEq, Copy, Clone, Debug, Hash)]
pub struct ModuleIdx(usize);

impl ModuleIdx {
    pub fn from_raw(index: usize) -> Self {
        Self(index)
    }
}

#[inline(always)]
pub fn timed<T>(op: impl FnOnce() -> T, level: log::Level, on_elapsed: impl FnOnce(Duration)) -> T {
    if log_enabled!(level) {
        let begin = Instant::now();
        let result = op();
        on_elapsed(begin.elapsed());
        result
    } else {
        op()
    }
}

pub trait ParserBackend: Sync {
    fn parse_module<'ast, 'alloc>(
        &self,
        resolver: &mut impl ModuleResolver,
        path: &Path,
        contents: &str,
        allocator: &'alloc impl AstAllocator<'ast, 'alloc>,
    ) -> ParseResult<ast::Module<'ast>>
    where
        'ast: 'alloc;

    fn parse_statement<'ast, 'alloc>(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &str,
        allocator: &'alloc impl AstAllocator<'ast, 'alloc>,
    ) -> ParseResult<AstNode<'ast, ast::Statement<'ast>>>
    where
        'ast: 'alloc;
}

pub trait ModuleResolver {
    fn add_module(
        &mut self,
        import_path: impl AsRef<Path>,
        location: Option<SourceLocation>,
    ) -> ParseResult<ModuleIdx>;
}

fn parse_file<'ast, 'alloc>(
    resolved_filename: impl AsRef<Path>,
    resolver: &mut impl ModuleResolver,
    backend: &impl ParserBackend,
    allocator: &'alloc impl AstAllocator<'ast, 'alloc>,
) -> Result<(ast::Module<'ast>, String), ParseError>
where
    'ast: 'alloc,
{
    debug!("Parsing file: {:?}", resolved_filename.as_ref());

    // load the file in...
    let source = fs::read_to_string(resolved_filename.as_ref())
        .map_err(|e| (e, resolved_filename.as_ref().to_owned()))?;

    let module = timed(
        || backend.parse_module(resolver, resolved_filename.as_ref(), &source, allocator),
        Level::Debug,
        |elapsed| debug!("ast: {:.2?}", elapsed),
    )?;

    Ok((module, source))
}

/// Represents an object that is responsible for resolving any module imports
pub struct SeqModuleResolver<'ast, 'alloc, 'backend, 'modules, B, A> {
    modules: &'modules mut Modules<'ast>,
    root_dir: PathBuf,
    backend: &'backend B,
    index: Option<ModuleIdx>,
    allocator: &'alloc A,
}

impl<'ast, 'alloc, 'backend, 'modules, B, A>
    SeqModuleResolver<'ast, 'alloc, 'backend, 'modules, B, A>
where
    B: ParserBackend,
    A: AstAllocator<'ast, 'alloc>,
    'ast: 'backend,
    'ast: 'modules,
    'ast: 'alloc,
{
    fn new(
        modules: &'modules mut Modules<'ast>,
        root_dir: PathBuf,
        backend: &'backend B,
        index: Option<ModuleIdx>,
        allocator: &'alloc A,
    ) -> Self {
        SeqModuleResolver {
            modules,
            root_dir,
            backend,
            index,
            allocator,
        }
    }

    fn for_module<R>(
        &mut self,
        mut dir: PathBuf,
        index: Option<ModuleIdx>,
        cb: impl FnOnce(&mut Self) -> R,
    ) -> R {
        mem::swap(&mut self.root_dir, &mut dir);
        let old_index = self.index;
        self.index = index;
        let ret = cb(self);
        self.index = old_index;
        mem::swap(&mut self.root_dir, &mut dir);
        ret
    }
}

impl<'ast, 'alloc, 'backend, 'modules, B, A> ModuleResolver
    for SeqModuleResolver<'ast, 'alloc, 'backend, 'modules, B, A>
where
    B: ParserBackend,
    A: AstAllocator<'ast, 'alloc>,
    'ast: 'backend,
    'ast: 'modules,
    'ast: 'alloc,
{
    fn add_module(
        &mut self,
        import_path: impl AsRef<Path>,
        location: Option<SourceLocation>,
    ) -> ParseResult<ModuleIdx> {
        let resolved_path = resolve_path(import_path, &self.root_dir, location)?;

        if let Some(module) = self.modules.get_by_path(&resolved_path) {
            let index = module.index();
            drop(module);

            if let Some(parent) = self.index {
                self.modules.add_dependency(parent, index);
            }
            return Ok(index);
        }

        let resolved_dir = resolved_path.parent().unwrap().to_owned(); // is this correct?

        let index = self.modules.next_index();

        let (node, source) = self.for_module(resolved_dir, Some(index), |resolver| {
            parse_file(
                &resolved_path,
                resolver,
                resolver.backend,
                resolver.allocator,
            )
        })?;

        // FIXME: this is broken, the index will already be updated!
        self.modules.add_module(resolved_path, node, source);

        if let Some(parent) = self.index {
            self.modules.add_dependency(parent, index);
        }
        Ok(index)
    }
}

// struct ParModuleResolver<'scope> {
//     sender: Sender<ParMessage>,
//     parent: Option<ModuleIdx>,
//     module_counter: &'scope AtomicUsize,
//     root_dir: PathBuf,
// }

// impl<'scope> ParModuleResolver<'scope> {
//     pub fn new(
//         sender: Sender<ParMessage>,
//         module_counter: &'scope AtomicUsize,
//         parent: Option<ModuleIdx>,
//         root_dir: PathBuf,
//     ) -> Self {
//         ParModuleResolver {
//             sender,
//             parent,
//             module_counter,
//             root_dir,
//         }
//     }

//     pub fn add_module_send_error(
//         &mut self,
//         import_path: impl AsRef<Path>,
//         location: Option<Location>,
//     ) -> Option<ModuleIdx> {
//         match self.add_module(import_path, location) {
//             Ok(index) => Some(index),
//             Err(err) => {
//                 self.sender.send(ParMessage::Error(err)).unwrap();
//                 None
//             }
//         }
//     }

//     fn for_dir<R>(&mut self, mut dir: PathBuf, cb: impl FnOnce(&mut Self) -> R) -> R {
//         mem::swap(&mut self.root_dir, &mut dir);
//         let ret = cb(self);
//         mem::swap(&mut self.root_dir, &mut dir);
//         ret
//     }

//     fn parse_file(
//         &mut self,
//         resolved_filename: impl AsRef<Path>,
//         backend: &impl for<'a> ParserBackend<'a>,
//     ) {
//         let parse_result = self.for_dir(self.root_dir.to_owned(), |resolver| {
//             let src;
//             let node = OwnedModule::try_new::<ParseError, _>(|bump| {
//                 let (node, source) = parse_file(&resolved_filename, resolver, backend, bump)?;
//                 src = source;
//                 Ok(node)
//             });
//             node.map(|n| (n, src))
//         });

//         let message = match parse_result {
//             Ok((node, source)) => ParMessage::ParsedModule {
//                 node,
//                 contents: source,
//                 filename: resolved_filename.as_ref().to_owned(),
//             },
//             Err(err) => ParMessage::Error(err),
//         };

//         self.sender.send(message).unwrap();
//     }
// }

// impl<'scope> ModuleResolver for ParModuleResolver<'scope> {
//     fn add_module(
//         &mut self,
//         import_path: impl AsRef<Path>,
//         location: Option<Location>,
//     ) -> ParseResult<ModuleIdx> {
//         let resolved_path = resolve_path(import_path, &self.root_dir, location)?;
//         let index = ModuleIdx(self.module_counter.fetch_add(1, Ordering::SeqCst));

//         self.sender
//             .send(ParMessage::ModuleImport {
//                 index,
//                 filename: resolved_path,
//                 parent: self.parent,
//             })
//             .unwrap();

//         Ok(index)
//     }
// }

/// Represents a set of loaded modules.
#[derive(Debug)]
pub struct Modules<'ast> {
    path_to_index: HashMap<PathBuf, ModuleIdx>,
    filenames_by_index: Vec<PathBuf>,
    modules_by_index: Vec<ast::Module<'ast>>,
    contents_by_index: Vec<String>,
    deps_by_index: Vec<HashSet<ModuleIdx>>,
    entry_point: Option<ModuleIdx>,
    size: usize,
}

impl<'ast, 'modules> Modules<'ast>
where
    Self: 'modules,
{
    /// Create a new [Modules] object
    pub fn new() -> Self {
        Modules {
            path_to_index: HashMap::new(),
            modules_by_index: vec![],
            deps_by_index: vec![],
            filenames_by_index: vec![],
            contents_by_index: vec![],
            entry_point: None,
            size: 0,
        }
    }

    pub fn has_index(&self, index: ModuleIdx) -> bool {
        self.size > index.0
    }

    pub fn has_path(&self, path: impl AsRef<Path>) -> bool {
        self.path_to_index.contains_key(path.as_ref())
    }

    pub fn get_by_index(&'modules self, index: ModuleIdx) -> Module<'ast, 'modules> {
        self.get_by_index_checked(index).unwrap()
    }

    pub fn get_modules(&self) -> &Vec<ast::Module<'ast>> {
        &self.modules_by_index
    }

    pub fn has_entry_point(&self) -> bool {
        self.entry_point.is_some()
    }

    pub fn get_entry_point_checked(&'modules self) -> Option<Module<'ast, 'modules>> {
        Some(self.get_by_index(self.entry_point?))
    }

    pub fn get_entry_point(&'modules self) -> Module<'ast, 'modules> {
        self.get_entry_point_checked().unwrap()
    }

    pub fn get_by_index_checked(
        &'modules self,
        index: ModuleIdx,
    ) -> Option<Module<'ast, 'modules>> {
        if !self.has_index(index) {
            None
        } else {
            Some(Module {
                index,
                modules: self,
            })
        }
    }

    pub fn get_by_path(&'modules self, path: impl AsRef<Path>) -> Option<Module<'ast, 'modules>> {
        self.path_to_index
            .get(path.as_ref())
            .map(|&idx| self.get_by_index(idx))
    }

    pub fn get_by_path_unchecked(&'modules self, path: impl AsRef<Path>) -> Module<'ast, 'modules> {
        self.get_by_path(path).unwrap()
    }

    fn add_module(
        &'modules mut self,
        path: PathBuf,
        node: ast::Module<'ast>,
        contents: String,
    ) -> Module<'ast, 'modules> {
        let index = ModuleIdx(self.size);

        self.path_to_index.insert(path.clone(), index);
        self.filenames_by_index.push(path);
        self.modules_by_index.push(node);
        self.contents_by_index.push(contents);
        self.deps_by_index.push(HashSet::new());

        self.size += 1;

        Module {
            index,
            modules: self,
        }
    }

    fn next_index(&self) -> ModuleIdx {
        ModuleIdx(self.size)
    }

    fn set_entry_point(&mut self, index: ModuleIdx) {
        if !self.has_index(index) {
            panic!("Tried to set entry point of nonexistent module");
        }

        self.entry_point = Some(index);
    }

    fn add_dependency(&mut self, parent: ModuleIdx, child: ModuleIdx) {
        if !self.has_index(parent) {
            panic!("Tried to set dependency of nonexistent module");
        }
        self.deps_by_index[parent.0].insert(child);
    }
}

/// Represents a single module.
pub struct Module<'ast, 'modules> {
    index: ModuleIdx,
    modules: &'modules Modules<'ast>,
}

impl<'ast, 'modules> Module<'ast, 'modules>
where
    'ast: 'modules,
{
    pub fn all_modules(&self) -> &Modules<'ast> {
        self.modules
    }

    pub fn index(&self) -> ModuleIdx {
        self.index
    }

    pub fn is_entry_point(&self) -> bool {
        self.modules.entry_point == Some(self.index)
    }

    pub fn ast(&self) -> &ast::Module<'ast> {
        &self.modules.modules_by_index[self.index.0]
    }

    pub fn content(&self) -> &str {
        self.modules.contents_by_index[self.index.0].as_ref()
    }

    pub fn dependencies(&'modules self) -> impl Iterator<Item = Module<'ast, 'modules>> {
        self.modules.deps_by_index[self.index.0]
            .iter()
            .map(move |&index| Module {
                index,
                modules: self.modules,
            })
    }

    pub fn filename(&self) -> &Path {
        self.modules.filenames_by_index[self.index.0].as_ref()
    }
}

/// The location of a build directory of this package, this used to resolve where the standard library
/// is located at.
static BUILD_DIR: &str = env!("CARGO_MANIFEST_DIR");

/// Name of the prelude module
static PRELUDE: &str = "prelude";

// FIXME: this is what we should be looking at rather than doing at runtime!
// Module names that are used within the standard library
// const MODULES: &[&Path] = get_stdlib_modules!("./stdlib");
//
/// Function that builds a module map of the standard library that is shipped
/// with the compiler distribution. Standard library modules are referenced
/// within imports
pub fn get_stdlib_modules(dir: impl AsRef<Path>) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = Vec::new();

    if dir.as_ref().is_dir() {
        for entry in fs::read_dir(dir).unwrap() {
            match entry {
                Ok(p) => {
                    let path = p.path();

                    if path.is_dir() {
                        // recurse and get all of the files with the prefix
                        let prefix: &Path = path.file_stem().unwrap().as_ref();

                        for entry in get_stdlib_modules(path.as_path()) {
                            paths.push(prefix.join(entry));
                        }
                    } else if path.is_file() {
                        let file_name = path.file_stem().unwrap();

                        // Special case, don't add prelude to the module list since we don't want to allow
                        // it to be imported under the normal standard library imports.
                        if file_name == PRELUDE {
                            continue;
                        }

                        // This shouldn't happen but if there is a file which does not have a hash extension, we shouldn't add it
                        if path.extension().unwrap_or_default() != "hash" {
                            continue;
                        }

                        paths.push(PathBuf::from(file_name));
                    }
                }
                Err(e) => panic!("Unable to read standard library folder: {}", e),
            }
        }
    }

    paths
}

pub fn resolve_path(
    path: impl AsRef<Path>,
    wd: impl AsRef<Path>,
    location: Option<SourceLocation>,
) -> ParseResult<PathBuf> {
    let path = path.as_ref();
    let wd = wd.as_ref();

    let stdlib_path: PathBuf = [BUILD_DIR, "..", "stdlib"].iter().collect();
    let modules = get_stdlib_modules(stdlib_path);

    // check if the given path is equal to any of the standard library paths
    if modules.contains(&path.to_path_buf()) {
        return Ok(path.to_path_buf());
    }

    // otherwise, we have to resolve the module path based on the working directory
    let work_dir = wd.canonicalize().unwrap();
    let raw_path = work_dir.join(path);

    // If the provided path is a directory, we assume that the user is referencing an index
    // module that is located within the given directory. This takes precendence over checking
    // if a module is named that directory.
    // More info on this topic: https://hash-org.github.io/lang/modules.html#importing
    if raw_path.is_dir() {
        let idx_path = raw_path.join("index.hash");

        if idx_path.exists() {
            return Ok(idx_path);
        }

        // ok now check if the user is referencing a module instead of the dir
        let raw_path_hash = raw_path.with_extension("hash");
        if raw_path_hash.exists() {
            return Ok(raw_path_hash);
        }

        // @@Copied
        Err(ParseError::ImportError {
            import_name: path.to_path_buf(),
            src: location.unwrap_or_else(|| SourceLocation::interactive()),
        })
    } else {
        // we don't need to anything if the given raw_path already has a extension '.hash',
        // since we don't dissalow someone to import a module and reference the module with
        // the name, like so...
        //
        // > let lib = import("lib.hash");
        // same as...
        // > let lib = import("lib");

        match raw_path.extension() {
            Some(k) if k == "hash" => Ok(raw_path),
            _ => {
                // add hash extension regardless and check if the path exists...
                let raw_path_hash = raw_path.with_extension("hash");

                // Only try to check this route if the provided file did not already have an extension
                if raw_path.extension().is_none() && raw_path_hash.exists() {
                    Ok(raw_path_hash)
                } else {
                    Err(ParseError::ImportError {
                        import_name: path.to_path_buf(),
                        src: location.unwrap_or_else(|| SourceLocation::interactive()),
                    })
                }
            }
        }
    }
}
