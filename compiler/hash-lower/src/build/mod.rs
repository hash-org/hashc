//! Defines a IR Builder for function blocks. This is essentially a builder
//! pattern for lowering declarations into the associated IR.

mod block;
mod category;
mod constant;
mod into;
mod matches;
mod place;
mod rvalue;
mod temp;
mod ty;
mod utils;

use hash_attrs::{attr::attr_store, builtin::attrs};
use hash_ir::{
    ir::{
        BasicBlock, Body, BodyMetadata, BodySource, Local, LocalDecl, LocalDecls, Place,
        Projections, START_BLOCK, TerminatorKind,
    },
    ty::{Mutability, ReprTy},
};
use hash_source::identifier::Identifier;
use hash_storage::store::{SequenceStoreKey, statics::StoreId};
use hash_target::{HasTarget, Target};
use hash_tir::{
    context::{Context, HasContext, ScopeKind},
    tir::{FnDef, FnDefId, FnTy, HasAstNodeId, NodesId, SymbolId, TermId},
};
use hash_utils::{fxhash::FxHashMap, index_vec::IndexVec};

use crate::{cfg::ControlFlowGraph, ctx::BuilderCtx};

/// A wrapper type for the kind of TIR term that is being lowered, the [Builder]
/// accepts either a [FnDefId] or a [TermId]. The [TermId] case is used when a
/// constant block is being lowered.
#[derive(Clone, Copy)]
pub(crate) enum BuildItem {
    /// A function body is being lowered.
    FnDef(FnDefId),
    /// An arbitrary expression is being lowered, this is done
    /// for constant expressions.
    Const(TermId),
}

impl BuildItem {
    /// Convert the build item into the expression variant, if this is not
    /// an expression variant, then this will panic.
    pub fn as_const(&self) -> TermId {
        match self {
            BuildItem::FnDef(_) => unreachable!(),
            BuildItem::Const(term) => *term,
        }
    }

    /// Convert the build item into the function definition variant, if this is
    /// not a function definition variant, then this will panic.
    pub fn as_fn_def(&self) -> FnDefId {
        match self {
            BuildItem::FnDef(fn_def) => *fn_def,
            BuildItem::Const(_) => unreachable!(),
        }
    }
}

impl From<FnDefId> for BuildItem {
    fn from(fn_def: FnDefId) -> Self {
        BuildItem::FnDef(fn_def)
    }
}

impl From<TermId> for BuildItem {
    fn from(constant: TermId) -> Self {
        BuildItem::Const(constant)
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
pub(crate) struct BodyBuilder<'tcx> {
    /// The type storage needed for accessing the types of the traversed terms
    ctx: BuilderCtx<'tcx>,

    /// Info that is derived during the lowering process of the type.
    info: BodyMetadata,

    /// The item that is being lowered.
    item: BuildItem,

    /// Number of arguments that will be used in the function, for constant
    /// expressions, this will be zero.
    arg_count: usize,

    /// The body control-flow graph.
    control_flow_graph: ControlFlowGraph,

    /// Any local declarations that have been made.
    locals: LocalDecls,

    /// Any projections that have been applied within the currently constructed
    /// body.
    projections: Projections,

    /// A map that is used by the [Builder] to lookup which variables correspond
    /// to which locals.
    declaration_map: FxHashMap<SymbolId, Local>,

    /// Information about the currently traversed [ast::Block] in the AST. This
    /// value is used to determine when the block should be terminated by
    /// the builder. This is used to avoid lowering statements that occur
    /// after a block terminator.
    loop_block_info: Option<LoopBlockInfo>,

    /// If the lowerer has reached a terminating statement within some block,
    /// meaning that further statements do not require to be lowered.
    ///
    /// A statement that is typed as `!`. Examples of such statements
    /// are `return`, `break`, `continue`, or expressions that are of type
    /// `!`.
    reached_terminator: bool,

    /// A temporary [Place] that is used to throw away results from expressions
    /// when we know that we don't need or want to store the result. If
    /// `tmp_place` is [None], then we create a new temporary place and store
    /// it in the field for later use.
    tmp_place: Option<Place>,
}

impl HasTarget for BodyBuilder<'_> {
    fn target(&self) -> &Target {
        self.ctx.settings.target()
    }
}

impl HasContext for BodyBuilder<'_> {
    fn context(&self) -> &Context {
        self.ctx.context()
    }
}

impl<'ctx> BodyBuilder<'ctx> {
    pub(crate) fn new(name: Identifier, item: BuildItem, ctx: BuilderCtx<'ctx>) -> Self {
        let (arg_count, source) = match item {
            BuildItem::FnDef(fn_def) => {
                // Get the type of this function definition, we need to
                // figure out how many arguments there will be passed in
                // and how many locals we need to allocate.
                (fn_def.borrow().ty.params.len(), BodySource::Item)
            }
            BuildItem::Const(_) => (0, BodySource::Const),
        };

        // Compute the span of the item that was just lowered.
        let span = match item {
            BuildItem::FnDef(def) => def.node_id_or_default(),
            BuildItem::Const(term) => term.node_id_or_default(),
        };

        let mut info = BodyMetadata::new(name, source);

        // If the body needs to be dumped, then we mark it as such.
        if attr_store().node_has_attr(span, attrs::DUMP_IR) {
            info.dump = true;
        }

        Self {
            item,
            ctx,
            info,
            arg_count,
            control_flow_graph: ControlFlowGraph::new(),
            locals: IndexVec::new(),
            projections: Projections::new(),
            declaration_map: FxHashMap::default(),
            reached_terminator: false,
            loop_block_info: None,
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

        // Compute the span of the item that was just lowered.
        let span = match self.item {
            BuildItem::FnDef(def) => self.span_of_def(def),
            BuildItem::Const(term) => self.span_of_term(term),
        };

        Body::new(
            self.control_flow_graph.basic_blocks,
            self.locals,
            self.projections,
            self.info,
            self.arg_count,
            span,
        )
    }

    pub(crate) fn build(&mut self) {
        // lower the initial type and the create a
        let ty = match self.item {
            BuildItem::FnDef(fn_def) => self.ty_id_from_tir_fn_def(fn_def),
            BuildItem::Const(item) => self.ty_id_from_tir_term(item),
        };
        self.info.set_ty(ty);

        // If it is a function type, then we use the return type of the
        // function as the `return_ty`, otherwise we assume the type provided
        // is the `return_ty`
        let return_ty = ty.map(|item_ty| match item_ty {
            ReprTy::FnDef { instance } => instance.borrow().return_ty,
            _ => ty,
        });

        // The first local declaration is used as the return type. The return local
        // declaration is always mutable because it will be set at some point in
        // the end, not the beginning.
        let ret_local = LocalDecl::new_auxiliary(return_ty, Mutability::Mutable);
        self.locals.push(ret_local);

        match self.item {
            BuildItem::FnDef(_) => self.build_fn(),
            BuildItem::Const(_) => self.build_const(),
        }
    }

    /// This is the entry point for lowering functions into Hash IR.
    fn build_fn(&mut self) {
        let fn_def = self.item.as_fn_def();

        Context::enter_resolved_scope_mut(self, ScopeKind::Fn(fn_def), |this| {
            // The type must be a function type...
            let FnDef { ty: FnTy { params, .. }, body, .. } = *fn_def.value();

            params.elements().borrow().iter().for_each(|param| {
                let ir_ty = this.ty_id_from_tir_ty(param.ty);

                // @@Future: deal with parameter attributes that are mutable?
                this.push_local(param.name, LocalDecl::new_immutable(param.name.ident(), ir_ty));
            });

            this.build_body(body)
        })
    }

    /// Build a [Body] for a constant expression that occurs on the
    /// top-level of a module. If this function receives something that
    /// is non-constant, then the function will panic since it can't
    /// be sure that the provided block will be constant.
    ///
    /// This is a different concept from `compile-time` since in the future we
    /// will allow compile time expressions to run any arbitrary code.
    fn build_const(&mut self) {
        let node = self.item.as_const();

        // update the type in the body info with this value
        self.info.set_ty(self.ty_id_from_tir_term(node));
        self.build_body(node);
    }

    /// Function that builds the main body of a [BuildItem]. This will lower the
    /// expression that is provided, and store the result into the
    /// `RETURN_PLACE`.
    fn build_body(&mut self, body: TermId) {
        // Now we begin by lowering the body of the function.
        let start = self.control_flow_graph.start_new_block();
        debug_assert!(start == START_BLOCK);

        // Now that we have built the inner body block, we then need to terminate
        // the current basis block with a return terminator.
        let return_block = unpack!(self.term_into_dest(Place::return_place(), start, body));
        let span = self.span_of_term(body);

        self.control_flow_graph.terminate(return_block, span, TerminatorKind::Return);
    }
}
