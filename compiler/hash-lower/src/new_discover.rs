//! This module contains functionality to discover functions in the TIR tree in
//! order to lower them to IR.
//!
//! For now, non-pure functions are always queued for lowering.
use std::ops::ControlFlow;

use derive_more::{Constructor, Deref};
use hash_tir::new::{
    atom_info::ItemInAtomInfo,
    environment::env::AccessToEnv,
    fns::{FnBody, FnDefId},
    mods::ModMemberValue,
    terms::TermId,
    utils::{common::CommonUtils, traversing::Atom, AccessToUtils},
};
use indexmap::IndexSet;

/// Discoverer for functions to lower in the TIR tree.
#[derive(Constructor, Deref)]
pub struct FnDiscoverer<'a, T: AccessToEnv> {
    env: &'a T,
}

/// Stores a set of discovered functions.
#[derive(Debug, Clone, Default)]
pub struct DiscoveredFns {
    pub fns: IndexSet<FnDefId>,
}

impl DiscoveredFns {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a function to the set of discovered functions.
    pub fn add_fn(&mut self, fn_def: FnDefId) {
        self.fns.insert(fn_def);
    }
}

impl<T: AccessToEnv> FnDiscoverer<'_, T> {
    /// Discover all TIR runtime functions in the sources, in order to lower
    /// them to IR.
    pub fn discover_fns(&self) -> DiscoveredFns {
        let mut fns = DiscoveredFns::new();

        for mod_def_id in self.mod_utils().iter_all_mods() {
            for member in self.mod_utils().iter_mod_members(mod_def_id) {
                match member.value {
                    ModMemberValue::Mod(_) => {
                        // Will be handled later in the loop
                    }
                    ModMemberValue::Data(_) => {
                        // We don't need to discover anything in data types
                    }
                    ModMemberValue::Fn(fn_def_id) => {
                        let fn_def = self.get_fn_def(fn_def_id);

                        // @@Todo: in the future, we might want to have a special flag by the
                        // typechecker as to whether to lower something or not, rather than always
                        // not lowering pure functions.
                        if fn_def.ty.pure {
                            continue;
                        }

                        fns.add_fn(fn_def_id);

                        match fn_def.body {
                            FnBody::Defined(body) => {
                                // Add all nested functions too
                                let inferred_body = self.get_inferred_value(body);
                                self.add_all_child_fns(inferred_body, &mut fns);
                            }
                            FnBody::Intrinsic(_) | FnBody::Axiom => {
                                // Intrinsic and axiom functions have no defined
                                // bodies
                            }
                        }
                    }
                }
            }
        }

        fns
    }

    /// Add all the child functions of the given term to the given set of
    /// discovered functions.
    ///
    /// *Invariant*: The term must be inferred, i.e.
    /// `self.get_inferred_value(term) = term`
    fn add_all_child_fns(&self, term: TermId, fns: &mut DiscoveredFns) {
        self.traversing_utils()
            .visit_term::<!, _>(term, &mut |atom: Atom| match atom {
                Atom::Term(_) => Ok(ControlFlow::Continue(())),
                Atom::Ty(_) => Ok(ControlFlow::Break(())),
                Atom::FnDef(f) => {
                    // @@Todo: this doesn't deal with captures.
                    let f_val = self.get_fn_def(f);
                    if !f_val.ty.pure {
                        fns.add_fn(f);
                    }
                    Ok(ControlFlow::Continue(()))
                }
                Atom::Pat(_) => Ok(ControlFlow::Continue(())),
            })
            .into_ok();
    }
}
