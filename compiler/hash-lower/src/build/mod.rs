//! Defines a IR Builder for function blocks. This is essentially a builder
//! pattern for lowering declarations into the associated IR.
#![allow(clippy::too_many_arguments)]

mod block;
mod constant;
mod expr;
mod matches;
mod pat;
mod place;
mod rvalue;
mod temp;
mod ty;

use std::collections::{HashMap, HashSet};

use hash_ast::ast::{AstNodeId, AstNodeRef, Expr, FnDef};
use hash_ir::{
    ir::{BasicBlock, Body, BodySource, Local, LocalDecl, Place, TerminatorKind, START_BLOCK},
    ty::{IrTy, IrTyId, Mutability},
    IrStorage,
};
use hash_source::{identifier::Identifier, location::Span, SourceId, SourceMap};
use hash_types::{pats::Pat, scope::ScopeId, storage::GlobalStorage};
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey, Store};
use index_vec::IndexVec;

use self::ty::{convert_term_into_ir_ty, get_fn_ty_from_term, lower_term};
use crate::cfg::ControlFlowGraph;

/// A wrapper type for the kind of AST node that is being lowered, the [Builder]
/// accepts either a [FnDef] or an [Expr] node. The [Expr] node case is used
/// when a constant block is being lowered.
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
    storage: &'tcx mut IrStorage,

    /// The sources of the current program, this is only used
    /// to give more contextual panics when the compiler unexpectedly
    /// encounters an unexpected AST node, and thus it will emit a
    /// span when the compiler panics.
    source_map: &'tcx SourceMap,

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

    /// Any local declarations that have been made.
    declarations: IndexVec<Local, LocalDecl>,

    /// A map that is used by the [Builder] to lookup which variables correspond
    /// to which locals.
    declaration_map: HashMap<(ScopeId, Identifier), Local>,

    /// The current scope stack that builder is in.
    scope_stack: Vec<ScopeId>,

    /// Information about the currently traversed [Block] in the AST. This
    /// value is used to determine when the block should be terminated by
    /// the builder. This is used to avoid lowering statements that occur
    /// after a block terminator.
    loop_block_info: Option<LoopBlockInfo>,

    /// If the current [Block] has reached a terminating statement, i.e. a
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
    dead_ends: &'tcx HashSet<AstNodeId>,
}

impl<'tcx> Builder<'tcx> {
    pub(crate) fn new(
        name: Identifier,
        item: BuildItem<'tcx>,
        source_id: SourceId,
        tcx: &'tcx GlobalStorage,
        storage: &'tcx mut IrStorage,
        source_map: &'tcx SourceMap,
        dead_ends: &'tcx HashSet<AstNodeId>,
    ) -> Self {
        let arg_count = match item {
            BuildItem::FnDef(node) => {
                // Get the type of this function definition, we need to
                // figure out how many arguments there will be passed in
                // and how many locals we need to allocate.

                let term =
                    tcx.node_info_store.node_info(node.id()).map(|info| info.term_id()).unwrap();
                let fn_ty = get_fn_ty_from_term(term, tcx);

                fn_ty.params.len()
            }
            BuildItem::Expr(_) => 0,
        };

        Self {
            item,
            tcx,
            storage,
            source_map,
            name,
            arg_count,
            source_id,
            control_flow_graph: ControlFlowGraph::new(),
            declarations: IndexVec::new(),
            declaration_map: HashMap::new(),
            reached_terminator: false,
            loop_block_info: None,
            scope_stack: vec![],
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
            self.name,
            self.arg_count,
            // @@Todo: actually determine this properly
            BodySource::Item,
            self.item.span(),
            self.source_id,
        )
    }

    /// Function to get the associated [TermId] with the
    /// provided [AstNodeId].
    #[inline]
    fn get_ty_id_of_node(&self, id: AstNodeId) -> IrTyId {
        let term_id = self.tcx.node_info_store.node_info(id).map(|f| f.term_id()).unwrap();

        // We need to try and look up the type within the cache, if not
        // present then we create the type by converting the term into
        // the type.

        convert_term_into_ir_ty(term_id, self.tcx, self.storage)
    }

    /// Function to get the associated [Term] with the
    /// provided [AstNodeId].
    #[inline]
    fn get_ty_of_node(&self, id: AstNodeId) -> IrTy {
        let term_id = self.tcx.node_info_store.node_info(id).map(|f| f.term_id()).unwrap();

        lower_term(term_id, self.tcx, self.storage)
    }

    /// Function to get the associated [PatId] with the
    /// provided [AstNodeId].
    #[inline]
    fn get_pat_id_of_node(&self, id: AstNodeId) -> Pat {
        let pat_id = self.tcx.node_info_store.node_info(id).map(|f| f.pat_id()).unwrap();

        self.tcx.pat_store.get(pat_id)
    }

    /// Function to create a new [Place] that is used to ignore
    /// the results of expressions, i.e. blocks.
    pub(crate) fn make_tmp_unit(&mut self) -> Place {
        match &self.tmp_place {
            Some(tmp) => tmp.clone(),
            None => {
                let ty = IrTy::unit(self.storage);
                let ty_id = self.storage.ty_store().create(ty);

                let local = LocalDecl::new_auxiliary(ty_id, Mutability::Immutable);
                let local_id = self.declarations.push(local);

                let place = Place::from(local_id);
                self.tmp_place = Some(place.clone());

                place
            }
        }
    }

    /// Run a lowering operation whilst entering a new scope which is derived
    /// from the provided [AstNodeRef<Expr>].
    ///
    /// N.B. It is assumed that the related expression has an associated scope.
    pub(crate) fn with_scope<T, U>(
        &mut self,
        expr: AstNodeRef<U>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let scope_id = self.tcx.node_info_store.node_info(expr.id()).map(|f| f.scope_id()).unwrap();
        self.scope_stack.push(scope_id);

        let result = f(self);

        let popped = self.scope_stack.pop();
        debug_assert!(popped.is_some() && matches!(popped, Some(id) if id == scope_id));

        result
    }

    /// Get the current [ScopeId] that is being used within the builder.
    pub(crate) fn current_scope(&self) -> ScopeId {
        *self.scope_stack.last().unwrap()
    }

    /// Push a [LocalDecl] in the current [Builder] with the associated
    /// [ScopeId]. This will put the [LocalDecl] into the declarations, and
    /// create an entry in the lookup map so that the [Local] can be looked up
    /// via the name of the local and the scope that it is in.
    pub(crate) fn push_local(&mut self, decl: LocalDecl, scope: ScopeId) -> Local {
        let decl_name = decl.name;
        let index = self.declarations.push(decl);

        // If the declaration has a name i.e. not an auxiliary local, then
        // we can push it into the `declaration_map`.
        if let Some(name) = decl_name {
            self.declaration_map.insert((scope, name), index);
        }

        index
    }

    /// Get the [Local] associated with the provided [ScopeId] and [Identifier].
    pub(crate) fn lookup_local(&self, name: Identifier) -> Option<Local> {
        // We need to walk up the scopes, and then find the first scope
        // that contains this variable
        for scope_id in self.scope_stack.iter().rev() {
            match self.tcx.scope_store.map_fast(*scope_id, |scope| scope.get(name)) {
                // Found in this scope, return the member.
                Some(_) => {
                    return self.declaration_map.get(&(*scope_id, name)).copied();
                }
                // Continue to the next (higher) scope:
                None => continue,
            }
        }

        None
    }

    /// This is the entry point for lowering functions into Hash IR.
    pub(crate) fn build_fn(&mut self) {
        // Get the type of the function, and then add the local declarations
        let node = match self.item {
            BuildItem::FnDef(node) => node,
            BuildItem::Expr(_) => unreachable!(),
        };

        let term_id = self.tcx.node_info_store.node_info(node.id()).map(|f| f.term_id()).unwrap();

        // We need to get the underlying `FnTy` so that we can read the parameters
        let fn_term = match self.item {
            BuildItem::FnDef(_node) => get_fn_ty_from_term(term_id, self.tcx),
            BuildItem::Expr(_) => unreachable!(),
        };
        let fn_params =
            self.tcx.params_store.get_owned_param_list(fn_term.params).into_positional();

        let IrTy::Fn(params, ret_ty) = lower_term(term_id, self.tcx, self.storage) else {
            panic!("Expected a function type");
        };

        // The first local declaration is used as the return type. The return local
        // declaration is always mutable because it will be set at some point in
        // the end, not the beginning.
        let ret_local = LocalDecl::new_auxiliary(ret_ty, Mutability::Mutable);
        self.declarations.push(ret_local);

        // Deal with all the function parameters that are given to the function.
        let param_scope =
            self.tcx.node_info_store.node_info(node.id()).map(|f| f.scope_id()).unwrap();
        self.scope_stack.push(param_scope);

        // @@Future: deal with parameter attributes that are mutable?
        for (ir_ty, param) in self.storage.ty_list_store().get_vec(params).iter().zip(fn_params) {
            let param_name = param.name.unwrap();
            self.push_local(LocalDecl::new_immutable(param_name, *ir_ty), param_scope);
        }

        // Now we begin by lowering the body of the function.
        let start = self.control_flow_graph.start_new_block();
        debug_assert!(start == START_BLOCK);

        // Now that we have built the inner body block, we then need to terminate
        // the current basis block with a return terminator.
        let ret_span = node.span(); // @@Fixme: this should be the span of the ending part of the function body
                                    // span!

        let return_block =
            unpack!(self.expr_into_dest(Place::return_place(), start, node.body.fn_body.ast_ref()));

        self.control_flow_graph.terminate(return_block, ret_span, TerminatorKind::Return)
    }

    /// Build a [Body] for a constant expression that occurs on the
    /// top-level of a module. If this function receives something that
    /// is non-constant, then the function will panic since it can't
    /// be sure that the provided block will be constant.
    ///
    /// This is a different concept from `compile-time` since in the future we
    /// will allow compile time expressions to run any arbitrary code.
    fn _build_const(&mut self, _node: AstNodeRef<Expr>) {}
}
