//! Defines a IR Builder for function blocks. This is essentially a builder
//! pattern for lowering declarations into the associated IR.

mod block;
mod expr;
mod matches;
mod pat;

use hash_ast::ast::{AstNodeId, AstNodeRef, Expr, FnDef};
use hash_ir::{
    ir::{
        BasicBlock, BasicBlockData, Body, FnSource, Local, LocalDecl, Place, Terminator,
        TerminatorKind, START_BLOCK,
    },
    IrStorage,
};
use hash_source::{
    identifier::Identifier,
    location::{SourceLocation, Span},
    SourceId,
};
use hash_types::{
    fmt::PrepareForFormatting,
    nodes::NodeInfoTarget,
    pats::{Pat, PatId},
    storage::GlobalStorage,
    terms::{FnLit, FnTy, Level0Term, Level1Term, TermId, TermOld},
};
use hash_utils::store::{CloneStore, PartialStore, SequenceStoreKey};
use index_vec::IndexVec;

use crate::cfg::ControlFlowGraph;

///
pub(crate) enum BuildItem<'a> {
    /// A function body is being lowered.
    FnDef(AstNodeRef<'a, FnDef>),
    /// An arbitrary expression is being lowered, this is done
    /// for constant expressions.
    Expr(AstNodeRef<'a, Expr>),
}

impl<'a> BuildItem<'a> {
    /// Returns the span of the item being lowered.
    pub fn span(&self) -> Span {
        match self {
            BuildItem::FnDef(fn_def) => fn_def.span(),
            BuildItem::Expr(expr) => expr.span(),
        }
    }
}

impl<'a> From<AstNodeRef<'a, FnDef>> for BuildItem<'a> {
    fn from(fn_def: AstNodeRef<'a, FnDef>) -> Self {
        BuildItem::FnDef(fn_def)
    }
}

impl<'a> From<AstNodeRef<'a, Expr>> for BuildItem<'a> {
    fn from(expr: AstNodeRef<'a, Expr>) -> Self {
        BuildItem::Expr(expr)
    }
}

/// Get the [FnTy] from a given [TermId].
fn get_fn_ty_from_term(term: TermId, tcx: &GlobalStorage) -> FnTy {
    let term = tcx.term_store.get(term);

    match term {
        TermOld::Level0(Level0Term::FnLit(FnLit { fn_ty, .. })) => get_fn_ty_from_term(fn_ty, tcx),
        TermOld::Level1(Level1Term::Fn(fn_ty)) => fn_ty,
        _ => unreachable!(),
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
macro_rules! unpack {
    ($x:ident = $c:expr) => {{
        let BlockAnd(b, v) = $c;
        $x = b;
        v
    }};

    ($c:expr) => {{
        let BlockAnd(b, ()) = $c;
        b
    }};
}

/// The builder is responsible for lowering a body into the associated IR.

pub(crate) struct Builder<'tcx> {
    /// The type storage needed for accessing the types of the traversed terms
    tcx: &'tcx GlobalStorage,

    /// The IR storage needed for storing all of the created values and bodies
    storage: &'tcx mut IrStorage,

    /// The name with the associated body that this is building.
    name: Identifier,

    /// The item that is being lowered.
    item: BuildItem<'tcx>,

    /// The originating module of where this item is defined.
    source_id: SourceId,

    /// Number of arguments that will be used in the function, for constant
    /// expressions, this will be zero.
    arg_count: usize,

    /// The body control-flow graph.
    control_flow_graph: ControlFlowGraph,

    /// Any local declarations that have been made
    declarations: IndexVec<Local, LocalDecl>,

    /// If the body that is being built will need to be
    /// dumped.
    needs_dumping: bool,
}

impl<'tcx> Builder<'tcx> {
    pub(crate) fn new(
        name: Identifier,
        item: BuildItem<'tcx>,
        source_id: SourceId,
        tcx: &'tcx GlobalStorage,
        storage: &'tcx mut IrStorage,
        needs_dumping: bool,
    ) -> Self {
        let arg_count = match item {
            BuildItem::FnDef(node) => {
                // Get the type of this function definition, we need to
                // figure out how many arguments there will be passed in
                // and how many locals we need to allocate.

                let term = tcx.node_info_store.get(node.id()).map(|f| f.term_id()).unwrap();
                let fn_ty = get_fn_ty_from_term(term, tcx);

                fn_ty.params.len()
            }
            BuildItem::Expr(_) => 0,
        };

        Self {
            item,
            tcx,
            storage,
            name,
            arg_count,
            source_id,
            control_flow_graph: ControlFlowGraph::new(),
            declarations: IndexVec::new(),
            needs_dumping,
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
            self.name,
            self.arg_count,
            // @@Todo: actually determine this properly
            FnSource::Item,
            self.item.span(),
            self.source_id,
            self.needs_dumping,
        )
    }

    /// Function to get the associated [TermId] with the
    /// provided [AstNodeId].
    #[inline]
    fn get_term_id_of_ast_node(&self, id: AstNodeId) -> TermId {
        self.tcx.node_info_store.get(id).map(|f| f.term_id()).unwrap()
    }

    /// Function to get the associated [PatId] with the
    /// provided [AstNodeId].
    #[inline]
    fn get_pat_of_ast_node(&self, id: AstNodeId) -> Pat {
        let pat_id = self.tcx.node_info_store.get(id).map(|f| f.pat_id()).unwrap();

        self.tcx.pat_store.get(pat_id)
    }

    pub(crate) fn build_fn(&mut self) {
        // Get the type of the function, and then add the local declarations
        let node = match self.item {
            BuildItem::FnDef(node) => node,
            BuildItem::Expr(_) => unreachable!(),
        };

        let term = match self.item {
            BuildItem::FnDef(node) => self.get_term_id_of_ast_node(node.id()),
            BuildItem::Expr(node) => self.get_term_id_of_ast_node(node.id()),
        };

        let fn_ty = get_fn_ty_from_term(term, self.tcx);

        // The first local declaration is used as the return type. The return local
        // declaration is always mutable because it will be set at some point in
        // the end, not the beginning.
        self.declarations.push(LocalDecl::new_mutable(fn_ty.return_ty));

        // Deal with all the function parameters that are given to the function.
        for param in self.tcx.params_store.get_owned_param_list(fn_ty.params).positional() {
            // @@Future: deal with parameter attributes that are mutable?
            self.declarations.push(LocalDecl::new_immutable(param.ty));
        }

        // Now we begin by lowering the body of the function.
        let start = self.control_flow_graph.start_new_block();
        debug_assert!(start == START_BLOCK);

        self.expr_into_dest(Place::return_place(), start, node.body.fn_body.ast_ref());
    }

    /// Build a [Body] for a constant expression that occurs on the
    /// top-level of a module. If this function receives something that
    /// is non-constant, then the function will panic since it can't
    /// be sure that the provided block will be constant.
    ///
    /// This is a different concept from `compile-time` since in the future we
    /// will allow compile time expressions to run any arbitrary code.
    fn build_const(&mut self, _node: AstNodeRef<Expr>) {}
}
