use hash_ast::ast::{self, AstNodeRef};
use hash_ir::{
    ir::{BasicBlock, LocalDecl, Place},
    ty::{IrTyId, Mutability},
};
use hash_source::identifier::Identifier;
use hash_types::pats::{BindingPat, Pat};
use hash_utils::store::Store;

use super::{BlockAnd, Builder};
use crate::build::{unpack, BlockAndExtend};

impl<'tcx> Builder<'tcx> {
    /// Visit all of the bindings that are declared in the current pattern, and
    /// add them to the current builder declarations.
    pub(crate) fn visit_bindings(&mut self, pat: AstNodeRef<'tcx, ast::Pat>) {
        let node_id = pat.id();

        match pat.body {
            ast::Pat::Binding(ast::BindingPat { name: _, visibility: _, mutability: _ }) => {
                // resolve the type of this binding
                let (name, mutability) =
                    self.tcx.pat_store.map_fast(self.pat_id_of_node(node_id), |pat| {
                        let Pat::Binding(BindingPat { mutability, name, .. }) = pat else {
                            unreachable!("expected binding pattern");
                        };

                        (*name, (*mutability).into())
                    });

                let ty = self.ty_id_of_node(node_id);
                self.declare_binding(name, ty, mutability)
            }
            ast::Pat::Tuple(ast::TuplePat { fields }) => {
                // @@Todo: deal with associating a projection here.

                for tuple_entry in fields.iter() {
                    let ast::TuplePatEntry { pat, .. } = tuple_entry.body();
                    self.visit_bindings(pat.ast_ref());
                }
            }
            ast::Pat::Constructor(_) => unimplemented!(),
            ast::Pat::List(_) => unimplemented!(),
            ast::Pat::Or(_) => unimplemented!(),
            ast::Pat::If(_) => unimplemented!(),
            ast::Pat::Lit(_)
            | ast::Pat::Module(_)
            | ast::Pat::Access(_)
            | ast::Pat::Range(_)
            | ast::Pat::Wild(_)
            | ast::Pat::Spread(_) => {}
        }
    }

    /// Declare a [Local] with the given metadata in the current builder.
    fn declare_binding(&mut self, name: Identifier, ty: IrTyId, mutability: Mutability) {
        let local = LocalDecl::new(name, mutability, ty);
        let scope_id = self.scope_stack.last().unwrap();

        self.push_local(local, *scope_id);
    }

    /// Put the right-hand side expression into the provided irrefutable
    /// pattern.
    pub(super) fn expr_into_pat(
        &mut self,
        mut block: BasicBlock,
        irrefutable_pat: AstNodeRef<'tcx, ast::Pat>,
        rvalue: AstNodeRef<'tcx, ast::Expr>,
    ) -> BlockAnd<()> {
        match irrefutable_pat.body {
            // The simple case of a just writing into the binding, we can
            // directly assign into the binding that is provided.
            ast::Pat::Binding(ast::BindingPat { name, .. }) => {
                let place = Place::from(self.lookup_local(name.ident).unwrap());
                unpack!(block = self.expr_into_dest(place, block, rvalue));
                block.unit()
            }
            ast::Pat::Wild(_) => unimplemented!(),
            ast::Pat::Constructor(_) => unimplemented!(),
            ast::Pat::Tuple(_) => unimplemented!(),
            ast::Pat::List(_) => unimplemented!(),
            ast::Pat::Lit(_) => unimplemented!(),
            ast::Pat::Or(_) => unimplemented!(),
            pat => {
                panic!("reached irrefutable pattern: {pat:?} in `expr_into_pat`");
            }
        }
    }
}
