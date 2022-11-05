use hash_ast::ast::{AstNodeRef, BlockExpr, Declaration, Expr, UnsafeExpr};
use hash_ir::ir::{BasicBlock, Place, RValue};
use hash_reporting::macros::panic_on_span;
use hash_utils::store::PartialStore;

use super::{unpack, BlockAnd, BlockAndExtend, Builder};

impl<'tcx> Builder<'tcx> {
    pub(crate) fn expr_into_dest(
        &mut self,
        destination: Place,
        mut block: BasicBlock,
        expr: AstNodeRef<'tcx, Expr>,
    ) -> BlockAnd<()> {
        let span = expr.span();

        let block_and = match expr.body {
            // @@Todo: we need to determine if this is a method call, or
            // a constructor call, we should do this somewhere else
            Expr::ConstructorCall(..) => todo!(),
            Expr::Directive(expr) => {
                self.expr_into_dest(destination, block, expr.subject.ast_ref())
            }
            Expr::Variable(variable) => {
                let term = self.get_ty_of_node(expr.id());
                let place = unpack!(block = self.as_place(block, expr));

                let rvalue = self.storage.push_rvalue(RValue::Use(place));
                self.control_flow_graph.push_assign(block, destination, rvalue, span);

                block.unit()
            }
            Expr::Access(..) => todo!(),
            Expr::Ref(..) => todo!(),
            Expr::Deref(..) => todo!(),
            Expr::Unsafe(UnsafeExpr { data }) => {
                self.expr_into_dest(destination, block, data.ast_ref())
            }

            // Lower this as an Rvalue
            Expr::Lit(literal) => {
                let constant = self.as_constant(literal.data.ast_ref());
                let rvalue = self.storage.push_rvalue(RValue::Const(constant));
                self.control_flow_graph.push_assign(block, destination, rvalue, span);

                block.unit()
            }

            // For declarations, we have to perform some bookkeeping in regards
            // to locals..., but this expression should never return any value
            // so we should just return a unit block here
            Expr::Declaration(decl) => self.handle_expr_declaration(block, decl),

            // Traverse the lhs of the cast, and then apply the cast
            // to the result... although this should be a no-op?
            Expr::Cast(..) => todo!(),

            // This includes `loop { ... } `, `{ ... }`, `match { ... }`
            Expr::Block(BlockExpr { data }) => {
                self.block_into_dest(destination, block, data.ast_ref())
            }

            // We never do anything for these anyway...
            Expr::Import { .. }
            | Expr::StructDef { .. }
            | Expr::EnumDef { .. }
            | Expr::TyFnDef { .. }
            | Expr::TraitDef { .. }
            | Expr::TraitImpl { .. }
            | Expr::MergeDeclaration { .. }
            | Expr::Ty { .. } => block.unit(),

            // We either need to lower the function as well, or perform
            // special treatment since this becomes a closure...
            Expr::FnDef(..) => todo!(),

            Expr::Assign { .. } | Expr::AssignOp { .. } => {
                todo!()
            }

            // @@Todo: For a return expression, we need to terminate this block, and
            // then return the value from the function.
            Expr::Return(..) => todo!(),

            // These should be unreachable in this context
            Expr::Continue { .. } | Expr::Break { .. } => unreachable!(),

            Expr::Index(..) => todo!(),
            Expr::BinaryExpr(..) => todo!(),
            Expr::UnaryExpr(..) => todo!(),
        };

        block_and
    }

    /// This function handles the lowering of an expression declaration.
    /// Internally, we check if this declaration needs to be lowered since
    /// this might be declaring a free function within the current function
    /// body, and thus we should not lower it.
    ///
    /// @@Todo: deal with non-trivial dead-ends, i.e. compound patterns that
    /// have dead ends...
    pub(crate) fn handle_expr_declaration(
        &mut self,
        block: BasicBlock,
        decl: &'tcx Declaration,
    ) -> BlockAnd<()> {
        if self.dead_ends.contains(&decl.pat.id()) {
            return block.unit();
        }

        // Declare all locals that need to be declared based on the
        // pattern.
        self.visit_bindings(decl.pat.ast_ref());

        if let Some(rvalue) = &decl.value {
            self.expr_into_pat(block, decl.pat.ast_ref(), rvalue.ast_ref());
        } else {
            panic_on_span!(
                decl.pat.span().into_location(self.source_id),
                self.source_map,
                "expected initialisation value, declaration are expected to have values (for now)."
            );
        }

        // if the declaration has an initialiser, then we need to deal with
        // the initialisation block.
        block.unit()
    }
}
