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

use hash_intrinsics::intrinsics::{AccessToIntrinsics, DefinedIntrinsics};
use hash_ir::{
    ir::{
        BasicBlock, Body, BodyInfo, BodySource, Local, LocalDecl, Place, TerminatorKind,
        UnevaluatedConst, START_BLOCK,
    },
    ty::{IrTy, Mutability},
};
use hash_pipeline::settings::CompilerSettings;
use hash_source::identifier::Identifier;
use hash_storage::store::{statics::StoreId, SequenceStoreKey};
use hash_target::{HasTarget, Target};
use hash_tir::{
    context::{Context, ScopeKind},
    environment::env::{AccessToEnv, Env},
    fns::{FnBody, FnDef, FnDefId, FnTy},
    symbols::Symbol,
    terms::TermId,
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

    /// The stage settings, sometimes used to determine what the lowering
    /// behaviour should be.
    settings: &'tcx CompilerSettings,

    /// Info that is derived during the lowering process of the type.
    info: BodyInfo,

    /// The item that is being lowered.
    item: BuildItem,

    /// Number of arguments that will be used in the function, for constant
    /// expressions, this will be zero.
    arg_count: usize,

    /// The body control-flow graph.
    control_flow_graph: ControlFlowGraph,

    /// Any local declarations that have been made.
    declarations: IndexVec<Local, LocalDecl>,

    /// Constants that will need to be resolved after all IR
    /// is built.
    // @@Unused: If we need to resolve constants after TIR, then this field
    // will be needed, but currently it is not used.
    _needed_constants: Vec<UnevaluatedConst>,

    /// A map that is used by the [Builder] to lookup which variables correspond
    /// to which locals.
    declaration_map: FxHashMap<Symbol, Local>,

    /// Information about the currently traversed [ast::Block] in the AST. This
    /// value is used to determine when the block should be terminated by
    /// the builder. This is used to avoid lowering statements that occur
    /// after a block terminator.
    loop_block_info: Option<LoopBlockInfo>,

    /// If the current [terms::BlockTerm] has reached a terminating statement,
    /// i.e. a statement that is typed as `!`. Examples of such statements
    /// are `return`, `break`, `continue`, etc.
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

impl<'ctx> AccessToEnv for BodyBuilder<'ctx> {
    fn env(&self) -> &Env {
        self.ctx.env
    }
}

impl<'ctx> AccessToIntrinsics for BodyBuilder<'ctx> {
    fn intrinsics(&self) -> &DefinedIntrinsics {
        self.ctx.intrinsics
    }
}

impl<'ctx> BodyBuilder<'ctx> {
    pub(crate) fn new(
        name: Identifier,
        item: BuildItem,
        tcx: BuilderCtx<'ctx>,
        settings: &'ctx CompilerSettings,
    ) -> Self {
        let (arg_count, source) = match item {
            BuildItem::FnDef(fn_def) => {
                // Get the type of this function definition, we need to
                // figure out how many arguments there will be passed in
                // and how many locals we need to allocate.
                (fn_def.borrow().ty.params.len(), BodySource::Item)
            }
            BuildItem::Const(_) => (0, BodySource::Const),
        };

        Self {
            settings,
            item,
            ctx: tcx,
            info: BodyInfo::new(name, source),
            arg_count,
            control_flow_graph: ControlFlowGraph::new(),
            declarations: IndexVec::new(),
            _needed_constants: Vec::new(),
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

        // @@ReAddDirectives: check if this item has a `#dump_ir` directive on it.
        //
        // check if this fn_def has the `#dump_ir` directive applied onto it...
        // let needs_dumping = <T>|item: | {
        // if let Some(applied_directives) = tir_stores().directives().borrow(item) {
        //     applied_directives.directives.contains(&IDENTS.dump_ir)
        // } else {
        //     false
        // }
        // };

        // Compute the span of the item that was just lowered.
        let (span, needs_dumping) = match self.item {
            BuildItem::FnDef(def) => {
                (self.span_of_def(def), false /* needs_dumping(def.into()) */)
            }
            BuildItem::Const(term) => {
                (self.span_of_term(term), false /* needs_dumping(term.into()) */)
            }
        };

        let mut body = Body::new(
            self.control_flow_graph.basic_blocks,
            self.declarations,
            self.info,
            self.arg_count,
            span,
        );

        // If the body needs to be dumped, then we mark it as such.
        if needs_dumping {
            body.mark_to_dump()
        }

        body
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
            IrTy::FnDef { instance } => instance.borrow().ret_ty,
            _ => ty,
        });

        // The first local declaration is used as the return type. The return local
        // declaration is always mutable because it will be set at some point in
        // the end, not the beginning.
        let ret_local = LocalDecl::new_auxiliary(return_ty, Mutability::Mutable);
        self.declarations.push(ret_local);

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
            let FnDef { ty: FnTy { params, .. }, body, .. } = fn_def.value();

            params.borrow().iter().for_each(|param| {
                let ir_ty = this.ty_id_from_tir_ty(param.ty);

                // @@Future: deal with parameter attributes that are mutable?
                this.push_local(param.name, LocalDecl::new_immutable(param.name.ident(), ir_ty));
            });

            // Axioms and Intrinsics are not lowered into IR
            let FnBody::Defined(body) = body else {
                panic!("defined function body was expected, but got `{body:?}`")
            };

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
