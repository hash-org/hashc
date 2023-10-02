use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    tir::{Term, Ty},
    visitor::{Atom, Visit, Visitor},
};
use hash_utils::log::info;

use crate::{env::TcEnv, tc::Tc};

impl<E: TcEnv> Tc<'_, E> {
    pub fn has_effects<N>(&self, node: N) -> Option<bool>
    where
        Visitor: Visit<N>,
    {
        let visitor = self.visitor();
        let mut has_effects = Some(false);
        visitor
            .visit(node, &mut |atom| self.atom_has_effects_once(&visitor, atom, &mut has_effects));
        has_effects
    }

    fn atom_has_effects_once(
        &self,
        visitor: &Visitor,
        atom: Atom,
        has_effects: &mut Option<bool>,
    ) -> ControlFlow<()> {
        match atom {
            Atom::Term(term) => match *term.value() {
                // Never has effects
                Term::Intrinsic(_) | Term::Hole(_) | Term::Fn(_) => ControlFlow::Break(()),

                // These have effects if their constituents do
                Term::Lit(_)
                | Term::Ctor(_)
                | Term::Tuple(_)
                | Term::Var(_)
                | Term::Match(_)
                | Term::Unsafe(_)
                | Term::Access(_)
                | Term::Array(_)
                | Term::Index(_)
                | Term::Cast(_)
                | Term::TyOf(_)
                | Term::DataTy(_)
                | Term::RefTy(_)
                | Term::Universe(_)
                | Term::TupleTy(_)
                | Term::FnTy(_)
                | Term::Block(_) => ControlFlow::Continue(()),

                Term::Call(fn_call) => {
                    // Get its inferred type and check if it is pure
                    match self.try_get_inferred_ty(fn_call.subject) {
                        Some(fn_ty) => {
                            match *fn_ty.value() {
                                Ty::FnTy(fn_ty) => {
                                    // If it is a function, check if it is pure
                                    if fn_ty.pure {
                                        // Check its args too
                                        visitor.visit(fn_call.args, &mut |atom| {
                                            self.atom_has_effects_once(visitor, atom, has_effects)
                                        });
                                        ControlFlow::Break(())
                                    } else {
                                        *has_effects = Some(true);
                                        ControlFlow::Break(())
                                    }
                                }
                                _ => {
                                    // If it is not a function, it is a function reference, which is
                                    // pure
                                    info!(
                                        "Found a function term that is not typed as a function: {}",
                                        fn_call.subject
                                    );
                                    ControlFlow::Break(())
                                }
                            }
                        }
                        None => {
                            // Unknown
                            *has_effects = None;
                            ControlFlow::Break(())
                        }
                    }
                }

                // These always have effects
                Term::Ref(_)
                | Term::Deref(_)
                | Term::Assign(_)
                | Term::Loop(_)
                | Term::LoopControl(_)
                | Term::Return(_) => {
                    *has_effects = Some(true);
                    ControlFlow::Break(())
                }
            },
            Atom::FnDef(fn_def_id) => {
                let fn_ty = fn_def_id.value().ty;
                // Check its params and return type only (no body)
                visitor.visit(fn_ty.params, &mut |atom| {
                    self.atom_has_effects_once(visitor, atom, has_effects)
                });
                visitor.visit(fn_ty.return_ty, &mut |atom| {
                    self.atom_has_effects_once(visitor, atom, has_effects)
                });
                ControlFlow::Break(())
            }
            Atom::Pat(_) => ControlFlow::Continue(()),
            Atom::Lit(_) => ControlFlow::Break(()),
        }
    }
}
