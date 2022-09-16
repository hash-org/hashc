//! Defines a IR Builder for function blocks. This is essentially a builder
//! pattern for lowering declarations into the associated IR.

use hash_ast::ast::{AstNodeRef, Expr, FnDef};
use hash_ir::ir::{BasicBlock, BasicBlockData, Body, Terminator, TerminatorKind};
use hash_source::location::{SourceLocation, Span};
use hash_types::storage::GlobalStorage;
use index_vec::IndexVec;

use crate::cfg::ControlFlowGraph;

pub struct Builder<'tcx> {
    /// The [Span] of the function and the function body
    span: SourceLocation,

    /// The number of arguments that is passed
    arg_count: usize,

    /// The type storage needed for accessing the types of the traversed terms
    tcx: &'tcx GlobalStorage,

    /// The body control-flow graph
    control_flow_graph: ControlFlowGraph<'tcx>,
}

impl<'tcx> Builder<'tcx> {
    fn build_fn(&mut self, _node: AstNodeRef<FnDef>) -> Body<'tcx> {
        todo!()
    }

    /// Build a [Body] for a constant expression that occurs on the
    /// top-level of a module. If this function receives something that
    /// is non-constant, then the function will panic since it can't
    /// be sure that the provided block will be constant.
    ///
    /// This is a different concept from `compile-time` since in the future we
    /// will allow compile time expressions to run any arbitrary code.
    fn build_const(&mut self, _node: AstNodeRef<Expr>) -> Body<'tcx> {
        todo!()
    }
}
