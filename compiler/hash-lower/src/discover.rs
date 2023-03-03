//! This module contains functionality to discover functions in the TIR tree in
//! order to lower them to IR.
//!
//! For now, non-pure functions are always queued for lowering.
use std::ops::ControlFlow;

use derive_more::{Constructor, Deref};
use hash_source::identifier::IDENTS;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    environment::env::AccessToEnv,
    fns::{FnBody, FnDef, FnDefId},
    mods::ModMemberValue,
    terms::TermId,
    utils::{common::CommonUtils, traversing::Atom, AccessToUtils},
};
use hash_utils::store::PartialCloneStore;
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

    /// Iterate over all discovered functions.
    pub fn iter(&self) -> impl Iterator<Item = &FnDefId> {
        self.fns.iter()
    }
}

impl<T: AccessToEnv> FnDiscoverer<'_, T> {
    /// Check whether a function definition needs to be lowered. The function
    /// should be lowered if it adheres to the following conditions:
    /// - It is not pure (for now)
    /// - It is not marked as "foreign"
    /// - It has a defined body
    /// - It is not an intrinsic or axiom
    pub fn fn_needs_to_be_lowered(&self, def_id: FnDefId, fn_def: &FnDef) -> bool {
        // @@Todo: in the future, we might want to have a special flag by the
        // typechecker as to whether to lower something or not, rather than always
        // not lowering pure functions.
        if fn_def.ty.pure {
            return false;
        }

        match fn_def.body {
            FnBody::Defined(_) => {
                // Check that the body is marked as "foreign" since
                // we don't want to lower it.
                if let Some(entry) = self.env().stores().directives().get(def_id.into()) {
                    if entry.directives.contains(&IDENTS.foreign) {
                        return false;
                    }
                }

                true
            }
            FnBody::Intrinsic(_) | FnBody::Axiom => {
                // Intrinsic and axiom functions have no defined
                // bodies

                false
            }
        }
    }

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

                        if self.fn_needs_to_be_lowered(fn_def_id, &fn_def) {
                            fns.add_fn(fn_def_id);

                            let FnBody::Defined(body) = fn_def.body else {
                                unreachable!()
                            };

                            // Add all nested functions too
                            let inferred_body = self.get_inferred_value(body);
                            self.add_all_child_fns(inferred_body, &mut fns);
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
                Atom::FnDef(def_id) => {
                    // @@Todo: this doesn't deal with captures.
                    let fn_def = self.get_fn_def(def_id);

                    if self.fn_needs_to_be_lowered(def_id, &fn_def) {
                        fns.add_fn(def_id);
                    }

                    Ok(ControlFlow::Continue(()))
                }
                Atom::Pat(_) => Ok(ControlFlow::Continue(())),
            })
            .into_ok();
    }
}
