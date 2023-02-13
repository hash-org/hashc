//! Defines a IR Builder for function blocks. This is essentially a builder
//! pattern for lowering declarations into the associated IR.
#![allow(clippy::too_many_arguments)]

mod block;
mod category;
mod constant;
mod expr;
mod matches;
mod place;
mod rvalue;
mod temp;
mod ty;
mod utils;

use std::collections::HashSet;

use hash_ast::ast;
use hash_ir::{
    ir::{
        BasicBlock, Body, BodyInfo, BodySource, Local, LocalDecl, Place, TerminatorKind,
        UnevaluatedConst, START_BLOCK,
    },
    ty::{IrTy, IrTyListId, Mutability},
    IrCtx,
};
use hash_pipeline::settings::CompilerSettings;
use hash_source::{identifier::Identifier, location::Span, SourceId, SourceMap};
use hash_tir::old::{scope::ScopeId, storage::GlobalStorage, terms::TermId};
use hash_utils::{
    index_vec::IndexVec,
    store::{FxHashMap, SequenceStore, SequenceStoreKey},
};

use self::ty::get_fn_ty_from_term;
use crate::cfg::ControlFlowGraph;

/// A wrapper type for the kind of AST node that is being lowered, the [Builder]
/// accepts either a [ast::FnDef] or an [ast::Expr] node. The [ast::Expr] node
/// case is used when a constant block is being lowered.
pub(crate) enum BuildItem<'a> {
    /// A function body is being lowered.
    FnDef(ast::AstNodeRef<'a, ast::FnDef>),
    /// An arbitrary expression is being lowered, this is done
    /// for constant expressions.
    Expr(ast::AstNodeRef<'a, ast::Expr>),
}

impl<'a> BuildItem<'a> {
    /// Returns the span of the item being lowered.
    pub fn span(&self) -> Span {
        match self {
            BuildItem::FnDef(fn_def) => fn_def.span(),
            BuildItem::Expr(expr) => expr.span(),
        }
    }

    /// Get the associated [ast::AstNodeId] with the [BuildItem].
    pub fn id(&self) -> ast::AstNodeId {
        match self {
            BuildItem::FnDef(fn_def) => fn_def.id(),
            BuildItem::Expr(expr) => expr.id(),
        }
    }

    /// Convert the build item into the expression variant, if this is not
    /// an expression variant, then this will panic.
    pub fn as_expr(&self) -> ast::AstNodeRef<'a, ast::Expr> {
        match self {
            BuildItem::FnDef(_) => unreachable!(),
            BuildItem::Expr(expr) => *expr,
        }
    }

    /// Convert the build item into the function definition variant, if this is
    /// not a function definition variant, then this will panic.
    pub fn as_fn_def(&self) -> ast::AstNodeRef<'a, ast::FnDef> {
        match self {
            BuildItem::FnDef(fn_def) => *fn_def,
            BuildItem::Expr(_) => unreachable!(),
        }
    }
}

impl<'a> From<ast::AstNodeRef<'a, ast::FnDef>> for BuildItem<'a> {
    fn from(fn_def: ast::AstNodeRef<'a, ast::FnDef>) -> Self {
        BuildItem::FnDef(fn_def)
    }
}

impl<'a> From<ast::AstNodeRef<'a, ast::Expr>> for BuildItem<'a> {
    fn from(expr: ast::AstNodeRef<'a, ast::Expr>) -> Self {
        BuildItem::Expr(expr)
    }
}

/// A monadic representation of a lowering context. Functions often need to
/// operate on the current block, potentially package the block, and return
/// some additional information that is outside of the block.
pub(crate) struct BlockAnd<T>(BasicBlock, T);

/// Trait used to defined operations on attaching information to
/// the block.
pub(crate) trait BlockAndExtend {
    /// The `block` and something...
    fn and<T>(self, v: T) -> BlockAnd<T>;
    /// Just the block.
    fn unit(self) -> BlockAnd<()>;
}

impl BlockAndExtend for BasicBlock {
    fn and<T>(self, v: T) -> BlockAnd<T> {
        BlockAnd(self, v)
    }

    fn unit(self) -> BlockAnd<()> {
        BlockAnd(self, ())
    }
}

/// Update a block pointer and return the value.
/// Use it like `let x = unpack!(block = self.foo(block, foo))`.
pub macro unpack {
    ($x:ident = $c:expr) => {{
        let BlockAnd(b, v) = $c;
        $x = b;
        v
    }},

    ($c:expr) => {{
        let BlockAnd(b, ()) = $c;
        b
    }}
}

/// Information about the current `loop` context that is being lowered. When
/// the [Builder] is lowering a loop, it will store the current loop body
/// block, and the `next` block that the loop will jump to after the loop
/// in order to correctly handle `break` and `continue` statements.
#[derive(Debug, Clone, Copy)]
pub(crate) struct LoopBlockInfo {
    /// Denotes where the index of the loop body that is being used
    /// for `continue` statements. The loop body should finish the
    /// current block by sending the **current** block to the loop body.
    loop_body: BasicBlock,

    /// Denotes where the index of the next block that is being used
    /// for `break` statements should jump to...
    next_block: BasicBlock,
}

/// The builder is responsible for lowering a body into the associated IR.
pub(crate) struct Builder<'tcx> {
    /// The type storage needed for accessing the types of the traversed terms
    tcx: &'tcx GlobalStorage,

    /// The IR storage needed for storing all of the created values and bodies
    ctx: &'tcx mut IrCtx,

    /// The sources of the current program, this is only used
    /// to give more contextual panics when the compiler unexpectedly
    /// encounters an unexpected AST node, and thus it will emit a
    /// span when the compiler panics.
    source_map: &'tcx SourceMap,

    /// The stage settings, sometimes used to determine what the lowering
    /// behaviour should be.
    settings: &'tcx CompilerSettings,

    /// Info that is derived during the lowering process of the type.
    info: BodyInfo,

    /// The item that is being lowered.
    item: BuildItem<'tcx>,

    /// The originating module of where this item is defined.
    source_id: SourceId,

    /// Number of arguments that will be used in the function, for constant
    /// expressions, this will be zero.
    arg_count: usize,

    /// The body control-flow graph.
    control_flow_graph: ControlFlowGraph,

    /// Any local declarations that have been made.
    declarations: IndexVec<Local, LocalDecl>,

    /// Constants that will need to be resolved after all IR
    /// is built.
    needed_constants: Vec<UnevaluatedConst>,

    /// A map that is used by the [Builder] to lookup which variables correspond
    /// to which locals.
    declaration_map: FxHashMap<(ScopeId, Identifier), Local>,

    /// The current scope stack that builder is in.
    scope_stack: Vec<ScopeId>,

    /// Information about the currently traversed [ast::Block] in the AST. This
    /// value is used to determine when the block should be terminated by
    /// the builder. This is used to avoid lowering statements that occur
    /// after a block terminator.
    loop_block_info: Option<LoopBlockInfo>,

    /// If the current [ast::Block] has reached a terminating statement, i.e. a
    /// statement that is typed as `!`. Examples of such statements are
    /// `return`, `break`, `continue`, etc.
    reached_terminator: bool,

    /// A temporary [Place] that is used to throw away results from expressions
    /// when we know that we don't need or want to store the result. If
    /// `tmp_place` is [None], then we create a new temporary place and store
    /// it in the field for later use.
    tmp_place: Option<Place>,

    /// Declaration dead ends, this is to ensure that we don't try to
    /// lower a declaration that is not part of the function definition.
    /// For example, if the function `foo` is declared in `bar` like this:
    /// ```ignore
    /// bar := () => {
    ///     foo := () => { 1 };   
    /// }
    /// ```
    ///
    /// Then we don't want to add `foo` as a declaration to the body of `bar`
    /// because it is a free standing function that will be lowered by
    /// another builder. However, this does not occur when the function is
    /// not free standing, for example:
    /// ```ignore
    /// bar := (x: i32) => {
    ///     foo := () => { 1 + x };   
    /// }
    /// ```
    /// The function `foo` is no longer free in `bar` because it captures `x`,
    /// therefore making it a closure of `foo`.
    dead_ends: &'tcx HashSet<ast::AstNodeId>,
}

impl<'ctx> Builder<'ctx> {
    pub(crate) fn new(
        name: Identifier,
        item: BuildItem<'ctx>,
        source_id: SourceId,
        scope_stack: Vec<ScopeId>,
        tcx: &'ctx GlobalStorage,
        ctx: &'ctx mut IrCtx,
        source_map: &'ctx SourceMap,
        dead_ends: &'ctx HashSet<ast::AstNodeId>,
        settings: &'ctx CompilerSettings,
    ) -> Self {
        let (arg_count, source) = match item {
            BuildItem::FnDef(node) => {
                // Get the type of this function definition, we need to
                // figure out how many arguments there will be passed in
                // and how many locals we need to allocate.
                let term =
                    tcx.node_info_store.node_info(node.id()).map(|info| info.term_id()).unwrap();
                let fn_ty = get_fn_ty_from_term(term, tcx);

                (fn_ty.params.len(), BodySource::Item)
            }
            BuildItem::Expr(_) => (0, BodySource::Const),
        };

        Self {
            settings,
            item,
            tcx,
            info: BodyInfo::new(name, source),
            ctx,
            source_map,
            arg_count,
            source_id,
            control_flow_graph: ControlFlowGraph::new(),
            declarations: IndexVec::new(),
            needed_constants: Vec::new(),
            declaration_map: FxHashMap::default(),
            reached_terminator: false,
            loop_block_info: None,
            scope_stack,
            dead_ends,
            tmp_place: None,
        }
    }

    /// Convert the [Builder] into the [Body].
    pub(crate) fn finish(self) -> Body {
        // Verify that all basic blocks have a terminator
        for (index, block) in self.control_flow_graph.basic_blocks.iter().enumerate() {
            if block.terminator.is_none() {
                panic!("Basic block {index} does not have a terminator");
            }
        }

        Body::new(
            self.control_flow_graph.basic_blocks,
            self.declarations,
            self.info,
            self.arg_count,
            self.item.span(),
            self.source_id,
        )
    }

    pub(crate) fn build(&mut self) {
        let item_id = self.item.id();
        let term = self.tcx.node_info_store.node_info(item_id).map(|f| f.term_id()).unwrap();

        // lower the initial type and the create a
        let ty = self.lower_term_as_id(term);
        self.info.set_ty(ty);

        // If it is a function type, then we use the return type of the
        // function as the `return_ty`, otherwise we assume the type provided
        // is the `return_ty`
        let (return_ty, params) = self.ctx.map_ty(ty, |item_ty| match item_ty {
            IrTy::FnDef { instance } => self
                .ctx
                .map_instance(*instance, |instance| (instance.ret_ty, Some(instance.params))),
            _ => (ty, None),
        });

        // The first local declaration is used as the return type. The return local
        // declaration is always mutable because it will be set at some point in
        // the end, not the beginning.
        let ret_local = LocalDecl::new_auxiliary(return_ty, Mutability::Mutable);
        self.declarations.push(ret_local);

        // Create a scope for the item, if one exists
        if let Some(scope) = self.tcx.node_info_store.node_info(item_id).unwrap().scope {
            self.scope_stack.push(scope);
        }

        match (&self.item, params) {
            (BuildItem::FnDef(_), Some(params)) => self.build_fn(term, params),
            (BuildItem::Expr(_), _) => self.build_const(),
            _ => unreachable!(),
        }
    }

    /// This is the entry point for lowering functions into Hash IR.
    fn build_fn(&mut self, term: TermId, param_tys: IrTyListId) {
        // Get the type of the function, and then add the local declarations
        let node = self.item.as_fn_def();

        // Deal with the function parameters
        let fn_term = get_fn_ty_from_term(term, self.tcx);
        let fn_params =
            self.tcx.params_store.get_owned_param_list(fn_term.params).into_positional();

        // Add each parameter as a declaration to the body.
        let scope = self.current_scope();
        for (index, param) in fn_params.iter().enumerate() {
            let ir_ty = self.ctx.tls().get_at_index(param_tys, index);
            let param_name = param.name.unwrap();

            // @@Future: deal with parameter attributes that are mutable?
            self.push_local(LocalDecl::new_immutable(param_name, ir_ty), scope);
        }

        self.build_body(node.body.fn_body.ast_ref())
    }

    /// Build a [Body] for a constant expression that occurs on the
    /// top-level of a module. If this function receives something that
    /// is non-constant, then the function will panic since it can't
    /// be sure that the provided block will be constant.
    ///
    /// This is a different concept from `compile-time` since in the future we
    /// will allow compile time expressions to run any arbitrary code.
    fn build_const(&mut self) {
        let node = self.item.as_expr();
        let term = self.tcx.node_info_store.node_info(node.id()).map(|f| f.term_id()).unwrap();

        // update the type in the body info with this value
        self.info.set_ty(self.lower_term_as_id(term));
        self.build_body(node);
    }

    /// Function that builds the main body of a [BuildItem]. This will lower the
    /// expression that is provided, and store the result into the
    /// `RETURN_PLACE`.
    fn build_body(&mut self, body: ast::AstNodeRef<'ctx, ast::Expr>) {
        // Now we begin by lowering the body of the function.
        let start = self.control_flow_graph.start_new_block();
        debug_assert!(start == START_BLOCK);

        // Now that we have built the inner body block, we then need to terminate
        // the current basis block with a return terminator.
        let return_block = unpack!(self.expr_into_dest(Place::return_place(self.ctx), start, body));

        self.control_flow_graph.terminate(return_block, body.span(), TerminatorKind::Return);
    }
}
