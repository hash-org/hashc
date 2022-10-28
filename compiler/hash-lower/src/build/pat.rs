use hash_ast::ast::{self, AstNodeRef};
use hash_ir::ir::{Local, LocalDecl};
use hash_types::{pats::BindingPat, scope::Mutability, terms::TermId};

use super::Builder;

impl<'a, 'tcx> Builder<'a, 'tcx> {
    /// Visit all of the bindings that are declared in the current pattern, and
    /// add them to the current builder declarations.
    pub(crate) fn visit_bindings(&mut self, pat: AstNodeRef<'a, ast::Pat>) {
        let pat_id = pat.id();

        match pat.body {
            ast::Pat::Binding(ast::BindingPat { name, visibility, mutability }) => {
                // resolve the type of this binding
                let pat = self.get_pat_of_ast_node(pat_id);
                let BindingPat { mutability, .. } = pat.into_bind().unwrap();

                let ty = self.get_term_id_of_ast_node(pat_id);
                self.declare_binding(ty, mutability)
            }
            ast::Pat::Constructor(_) => todo!(),
            ast::Pat::Tuple(ast::TuplePat { fields }) => {
                // @@Todo: deal with associating a projection here.

                for tuple_entry in fields.iter() {
                    let ast::TuplePatEntry { pat, .. } = tuple_entry.body();
                    self.visit_bindings(pat.ast_ref());
                }
            }
            ast::Pat::List(_) => todo!(),
            ast::Pat::Or(_) => todo!(),
            ast::Pat::If(_) => todo!(),
            ast::Pat::Lit(_)
            | ast::Pat::Module(_)
            | ast::Pat::Access(_)
            | ast::Pat::Range(_)
            | ast::Pat::Wild(_)
            | ast::Pat::Spread(_) => {}
        }
    }

    /// Declare a [Local] with the given metadata in the current builder.
    pub(crate) fn declare_binding(&mut self, ty: TermId, mutability: Mutability) {
        let local = LocalDecl::new(mutability, ty);

        self.declarations.push(local);
    }
}
