//! Utilities for checking if a term has effects, or if it is pure.
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
    /// Check if the given term has effects.
    ///
    /// Something is considered an effect if:
    /// - It mutates a variable,
    /// - It calls a function that is not pure,
    /// - It performs some imperative control-flow like a loop,
    /// - It operates on references.
    // @@Formalise: this is still a very vague notion of "effect", ideally we
    // want to have a very formal set of rules for this so that we don't lead into
    // inconsistencies with pure function evaluation.
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

    /// Check if the given atom has effects, for use with TIR `Visitor`'s `Map`
    /// trait.
    fn atom_has_effects_once(
        &self,
        visitor: &Visitor,
        atom: Atom,
        has_effects: &mut Option<bool>,
    ) -> ControlFlow<()> {
        match atom {
            Atom::Term(term) => {
                let (term_res, meta) = self.resolve_metas_and_vars(term);
                if meta.is_some() {
                    // Metas are always pure
                    *has_effects = Some(false);
                    return ControlFlow::Break(())
                }
                match *term_res.value() {
                    // Never has effects
                    Term::Intrinsic(_) | Term::Meta(_) | Term::Fn(_) => ControlFlow::Break(()),

                    // These have effects if their constituents do
                    Term::Lit(_)
                    | Term::Ctor(_)
                    | Term::Pat(_)
                    | Term::Tuple(_)
                    | Term::Var(_)
                    | Term::Match(_)
                    | Term::Unsafe(_)
                    | Term::Access(_)
                    | Term::Array(_)
                    | Term::Index(_)
                    | Term::Annot(_)
                    | Term::TyOf(_)
                    | Term::DataTy(_)
                    | Term::RefTy(_)
                    | Term::Universe(_)
                    | Term::TupleTy(_)
                    | Term::FnTy(_)
                    | Term::Block(_) => ControlFlow::Continue(()),

                    Term::Call(fn_call) => {
                        // Get its inferred type and check if it is pure
                        let Some(fn_ty) = self.try_get_inferred_ty(fn_call.subject) else {
                            // Unknown
                            *has_effects = None;
                            return ControlFlow::Break(())
                        };
                        let (fn_ty_res, meta) = self.resolve_metas_and_vars(fn_ty);
                        if meta.is_some() {
                            // If the type is a meta call, we don't know if it is effectful.
                            *has_effects = None;
                            ControlFlow::Break(())
                        } else {
                            match *fn_ty_res.value() {
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
                                    // If it is not a function, it is a function reference,
                                    // which is
                                    // pure
                                    info!(
                                        "Found a function term that is not typed as a function: {} : {}",
                                        fn_call.subject,
                                        fn_ty
                                    );
                                    ControlFlow::Break(())
                                }
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
            Atom::Lit(_) => ControlFlow::Break(()),
        }
    }
}
