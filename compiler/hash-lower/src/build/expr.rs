use hash_ast::ast::{AstNodeRef, BlockExpr, Expr, UnsafeExpr};
use hash_ir::ir::{BasicBlock, Place};
use hash_utils::store::PartialStore;

use super::{BlockAnd, BlockAndExtend, Builder};

impl<'a, 'tcx> Builder<'a, 'tcx> {
    pub(crate) fn expr_into_dest(
        &mut self,
        place: Place,
        block: BasicBlock,
        body: AstNodeRef<'a, Expr>,
    ) -> BlockAnd<()> {
        let block_and = match body.body {
            // @@Todo: we need to determine if this is a method call, or
            // a constructor call, we should do this somewhere else
            Expr::ConstructorCall(..) => todo!(),
            Expr::Directive(expr) => self.expr_into_dest(place, block, expr.subject.ast_ref()),
            Expr::Variable(variable) => {
                let term = self.tcx.node_info_store.get(body.id()).map(|f| f.term_id()).unwrap();
                println!("term: {term:?}");

                block.unit()
            }
            Expr::Access(..) => todo!(),
            Expr::Ref(..) => todo!(),
            Expr::Deref(..) => todo!(),
            Expr::Unsafe(UnsafeExpr { data }) => self.expr_into_dest(place, block, data.ast_ref()),

            // Lower this as an Rvalue
            Expr::Lit(..) => todo!(),

            // For declarations, we have to perform some bookkeeping in regards
            // to locals..., but this expression should never return any value
            // so we should just return a unit block here
            Expr::Declaration(decl) => self.handle_expr_declaration(place, block, body),

            // Traverse the lhs of the cast, and then apply the cast
            // to the result... although this should be a no-op?
            Expr::Cast(..) => todo!(),

            // This includes `loop { ... } `, `{ ... }`, `match { ... }`
            Expr::Block(BlockExpr { data }) => self.block_into_dest(place, block, data.ast_ref()),

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

    ///
    pub(crate) fn handle_expr_declaration(
        &mut self,
        place: Place,
        block: BasicBlock,
        body: AstNodeRef<'a, Expr>,
    ) -> BlockAnd<()> {
        // We need to declare all of the bindings within this declaration

        // if the declaration has an initialiser, then we need to deal with
        // the initialisation block.
        block.unit()
    }
}
