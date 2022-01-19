//! Hash Compiler pipeline implementation. The pipeline is a abstract representation
//! of the compiler flow managing the compiling steps like parsing, typechecking, optimisation
//! passes, etc. The pipeline is used to abstract away the idea of depending on specific
//! implementations of the parser or typechecker and just use a common trait
//! interface that can be used. This file also has definitions for how to access
//! sources whether module or interactive.
//!
//! @@Cleanup: Probably move all the source map stuff somewhere else?
//!
//!
//! All rights reserved 2022 (c) The Hash Language authors

pub mod fs;

use hash_ast::ast;
use hash_reporting::reporting::Report;
use hash_source::{InteractiveId, ModuleId, SourceId, SourceMap};
use hash_utils::timed;
use slotmap::SlotMap;
use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

#[derive(Debug)]
pub struct InteractiveBlock<'c> {
    contents: String,
    node: Option<ast::AstNode<'c, ast::BodyBlock<'c>>>,
}

impl<'c> InteractiveBlock<'c> {
    pub fn new(contents: String) -> Self {
        Self {
            contents,
            node: None,
        }
    }

    pub fn node(&self) -> ast::AstNodeRef<ast::BodyBlock<'c>> {
        self.node.as_ref().unwrap().ast_ref()
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn set_node(&mut self, node: ast::AstNode<'c, ast::BodyBlock<'c>>) {
        self.node = Some(node);
    }
}

#[derive(Debug)]
pub struct Module<'c> {
    path: PathBuf,
    contents: Option<String>,
    node: Option<ast::AstNode<'c, ast::Module<'c>>>,
}

impl<'c> Module<'c> {
    pub fn new(path: PathBuf) -> Self {
        Self {
            path,
            contents: None,
            node: None,
        }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn node(&self) -> ast::AstNodeRef<ast::Module<'c>> {
        self.node.as_ref().unwrap().ast_ref()
    }

    pub fn contents(&self) -> &str {
        self.contents.as_ref().unwrap()
    }

    pub fn set_node(&mut self, node: ast::AstNode<'c, ast::Module<'c>>) {
        self.node = Some(node);
    }

    pub fn set_contents(&mut self, contents: String) {
        self.contents = Some(contents);
    }
}

#[derive(Debug)]
pub enum Source<'c> {
    Interactive(InteractiveBlock<'c>),
    Module(Module<'c>),
}

#[derive(Debug, Copy, Clone)]
pub enum SourceRef<'i, 'c> {
    Interactive(&'i InteractiveBlock<'c>),
    Module(&'i Module<'c>),
}

#[derive(Debug, Default)]
pub struct Sources<'c> {
    interactive_offset: usize,
    interactive_blocks: SlotMap<InteractiveId, InteractiveBlock<'c>>,
    modules: SlotMap<ModuleId, Module<'c>>,
    module_paths: HashMap<PathBuf, ModuleId>,
    dependencies: HashMap<SourceId, HashSet<ModuleId>>,
}

impl<'c> Sources<'c> {
    pub fn new() -> Self {
        Self {
            interactive_offset: 0,
            interactive_blocks: SlotMap::with_key(),
            modules: SlotMap::with_key(),
            module_paths: HashMap::new(),
            dependencies: HashMap::new(),
        }
    }

    pub fn add_interactive_block(
        &mut self,
        interactive_block: InteractiveBlock<'c>,
    ) -> InteractiveId {
        self.interactive_offset += interactive_block.contents.len();
        self.interactive_blocks.insert(interactive_block)
    }

    pub fn add_module(&mut self, module: Module<'c>) -> ModuleId {
        let module_path = module.path.to_owned();
        let module_id = self.modules.insert(module);
        self.module_paths.insert(module_path, module_id);
        module_id
    }

    pub fn add_source(&mut self, source: Source<'c>) -> SourceId {
        match source {
            Source::Interactive(interactive_block) => {
                SourceId::Interactive(self.add_interactive_block(interactive_block))
            }
            Source::Module(module) => SourceId::Module(self.add_module(module)),
        }
    }

    pub fn get_interactive_block(&self, interactive_id: InteractiveId) -> &InteractiveBlock<'c> {
        self.interactive_blocks.get(interactive_id).unwrap()
    }

    pub fn get_interactive_block_mut(
        &mut self,
        interactive_id: InteractiveId,
    ) -> &mut InteractiveBlock<'c> {
        self.interactive_blocks.get_mut(interactive_id).unwrap()
    }

    pub fn get_module_mut(&mut self, module_id: ModuleId) -> &mut Module<'c> {
        self.modules.get_mut(module_id).unwrap()
    }

    pub fn get_module(&self, module_id: ModuleId) -> &Module<'c> {
        self.modules.get(module_id).unwrap()
    }

    pub fn get_module_id_by_path(&self, path: &Path) -> Option<ModuleId> {
        self.module_paths.get(path).copied()
    }

    pub fn get_module_by_path(&self, path: &Path) -> Option<&Module<'c>> {
        Some(self.get_module(self.get_module_id_by_path(path)?))
    }

    pub fn get_source(&self, source_id: SourceId) -> SourceRef<'_, 'c> {
        match source_id {
            SourceId::Interactive(interactive_id) => {
                SourceRef::Interactive(self.get_interactive_block(interactive_id))
            }
            SourceId::Module(module_id) => SourceRef::Module(self.get_module(module_id)),
        }
    }

    pub fn add_dependency(&mut self, source_id: SourceId, dependency: ModuleId) {
        self.dependencies
            .entry(source_id)
            .or_insert_with(HashSet::new)
            .insert(dependency);
    }
}

impl<'c> SourceMap for Sources<'c> {
    fn path_by_id(&self, source_id: SourceId) -> &Path {
        match self.get_source(source_id) {
            SourceRef::Interactive(_) => Path::new("<interactive>"),
            SourceRef::Module(module) => module.path(),
        }
    }

    fn contents_by_id(&self, source_id: SourceId) -> &str {
        match self.get_source(source_id) {
            SourceRef::Interactive(interactive) => interactive.contents(),
            SourceRef::Module(module) => module.contents(),
        }
    }
}

pub type CompilerResult<T> = Result<T, Report>;

/// The [Parser] represents an abstract parser that can parse all aspects of the Hash programming
/// language.
pub trait Parser<'c> {
    /// Given a [SourceId], parse the current job and append any parsed modules to the
    /// provided sources parameter. On success, the function returns nothing and on
    /// failure, the stage provides a generated diagnostics [Report].
    fn parse(&mut self, target: SourceId, sources: &mut Sources<'c>) -> CompilerResult<()>;
}

/// The [Checker] represents an abstract type checker that implements all the specified
/// typechecking methods and internally performs some kind of typechecking operations.
/// The methods [Checker::check_module] and [Checker::check_interactive] will return
/// a unit on success, or a generated diagnostic error report which can be displayed
/// and printed by the user of the pipeline. Both functions modify the states of the
/// checker and return them regardless of error, both states are considered to be the
/// new states and should be set in the compiler pipeline.
pub trait Checker<'c> {
    /// The general [Checker] state. This is implementation specific to the
    /// typechecker that implements this trait. The pipeline should have no
    /// dealings with the actual state, except saving it.
    type State;

    /// Make the general [Checker::State].
    fn make_state(&mut self) -> CompilerResult<Self::State>;

    /// The module typechecker state.
    type ModuleState;
    fn make_module_state(&mut self, state: &mut Self::State) -> CompilerResult<Self::ModuleState>;

    /// The interactive [Checker] state.
    type InteractiveState;

    /// Create an interactive [Checker] state.
    fn make_interactive_state(
        &mut self,
        state: &mut Self::State,
    ) -> CompilerResult<Self::InteractiveState>;

    /// Given a [InteractiveId], check the interactive statement with the specific rules
    /// that are applied in interactive rules. The function accepts the previous [Checker]
    /// state and previous [Checker::InteractiveState].
    fn check_interactive(
        &mut self,
        interactive_id: InteractiveId,
        sources: &Sources<'c>,
        state: &mut Self::State,
        interactive_state: Self::InteractiveState,
    ) -> (CompilerResult<()>, Self::InteractiveState);

    /// Given a [ModuleId], check the module. The function accepts the previous [Checker]
    /// state and [Checker::ModuleState]
    fn check_module(
        &mut self,
        module_id: ModuleId,
        sources: &Sources<'c>,
        state: &mut Self::State,
        module_state: Self::ModuleState,
    ) -> (CompilerResult<()>, Self::ModuleState);
}

/// The Hash Compiler interface. This interface allows a caller to create a
/// [Compiler] with the specified components. This allows external tinkerers
/// to add their own implementations of each compiler stage with relative ease
/// instead of having to scratch their heads.
pub struct Compiler<P, C> {
    /// The parser stage of the compiler.
    parser: P,
    /// The typechecking stage of the compiler.
    checker: C,
}

/// The [CompilerState] holds all the information and state of the compiler instance.
/// Each stage of the compiler contains a `State` type parameter which the compiler stores
/// so that incremental executions of the compiler are possible.
///
/// @@Future: Compiler metrics.
pub struct CompilerState<'c, C: Checker<'c>> {
    /// The collected workspace sources for the current job.
    pub sources: Sources<'c>,
    /// The typechecker state.
    pub checker_state: C::State,
    /// The interactive typechecker state. This mainly differs from the
    /// `module_checker_stage` by dealing with scopes slightly differently than module
    /// scope.
    pub checker_interactive_state: C::InteractiveState,
    /// The module checker stage.
    pub checker_module_state: C::ModuleState,
}

impl<'c, P, C> Compiler<P, C>
where
    P: Parser<'c>,
    C: Checker<'c>,
{
    /// Create a new instance of a [Compiler] with the provided parser and
    /// typechecker implementations.
    pub fn new(parser: P, checker: C) -> Self {
        Self { parser, checker }
    }

    /// Create a compiler state to accompany with compiler execution. Internally, this
    /// calls the [Checker] state making functions and saves it into the created
    /// [CompilerState].
    pub fn create_state(&mut self) -> CompilerResult<CompilerState<'c, C>> {
        let sources = Sources::new();
        let mut checker_state = self.checker.make_state()?;
        let checker_interactive_state = self.checker.make_interactive_state(&mut checker_state)?;
        let checker_module_state = self.checker.make_module_state(&mut checker_state)?;

        Ok(CompilerState {
            sources,
            checker_state,
            checker_interactive_state,
            checker_module_state,
        })
    }

    /// Run a interactive job with the provided [InteractiveId] pointing to the
    /// interpreted command to execute.
    pub fn run_interactive(
        &mut self,
        interactive_id: InteractiveId,
        mut compiler_state: CompilerState<'c, C>,
    ) -> (CompilerResult<()>, CompilerState<'c, C>) {
        // Parsing
        match self.parser.parse(
            SourceId::Interactive(interactive_id),
            &mut compiler_state.sources,
        ) {
            Ok(_) => {}
            Err(e) => return (Err(e), compiler_state),
        }

        // Typechecking
        let (result, checker_interactive_state) = self.checker.check_interactive(
            interactive_id,
            &compiler_state.sources,
            &mut compiler_state.checker_state,
            compiler_state.checker_interactive_state,
        );
        compiler_state.checker_interactive_state = checker_interactive_state;
        (result, compiler_state)
    }

    /// Run a module job with the provided [ModuleId] pointing to the entry point
    /// of the current job. Typically, the entry point is the first module that's
    /// passed from commandline arguments.
    pub fn run_module(
        &mut self,
        module_id: ModuleId,
        mut compiler_state: CompilerState<'c, C>,
    ) -> (CompilerResult<()>, CompilerState<'c, C>) {
        // Parsing
        let result = timed(
            || {
                self.parser
                    .parse(SourceId::Module(module_id), &mut compiler_state.sources)
            },
            log::Level::Debug,
            |elapsed| println!("parse: {:?}", elapsed),
        );

        if let Err(err) = result {
            return (Err(err), compiler_state);
        }

        // Typechecking
        timed(
            || {
                let (result, checker_module_state) = self.checker.check_module(
                    module_id,
                    &compiler_state.sources,
                    &mut compiler_state.checker_state,
                    compiler_state.checker_module_state,
                );

                compiler_state.checker_module_state = checker_module_state;
                (result, compiler_state)
            },
            log::Level::Debug,
            |elapsed| println!("typecheck: {:?}", elapsed),
        )
    }
}
