//! This module contains functionality to discover functions in the TIR tree in
//! order to lower them to IR.
//!
//! For now, non-pure functions are always queued for lowering.
use std::ops::ControlFlow;

use hash_attrs::{attr::attr_store, builtin::attrs};
use hash_pipeline::workspace::StageInfo;
use hash_storage::store::{statics::StoreId, Store, TrivialSequenceStoreKey};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    stores::tir_stores,
    tir::{FnDefId, HasAstNodeId, ModKind, ModMemberValue, TermId},
    visitor::{Atom, Visit, Visitor},
};
use hash_utils::{derive_more::Constructor, indexmap::IndexSet};

/// Discoverer for functions to lower in the TIR tree.
#[derive(Constructor)]
pub(crate) struct FnDiscoverer<'a> {
    /// A reference to [StageInfo] which refers to what the current
    /// status of each source is. This is used to avoid re-queuing modules
    /// that may of been queued in a previous run.
    stage_info: &'a StageInfo,
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
    pub fn add_fn(&mut self, def: FnDefId) {
        self.fns.insert(def);
    }

    pub fn contains(&self, def: FnDefId) -> bool {
        self.fns.contains(&def)
    }

    /// Iterate over all discovered functions.
    pub fn into_iter(self) -> impl Iterator<Item = FnDefId> {
        self.fns.into_iter()
    }
}

impl FnDiscoverer<'_> {
    /// Check whether a function definition needs to be lowered. The function
    /// should be lowered if it adheres to the following conditions:
    ///
    /// - It is not pure (for now)
    /// - It is not marked as "foreign"
    /// - It has a defined body
    /// - It is not an intrinsic or axiom
    ///
    /// If the function is to be queued, this will return the `body` of the
    /// function so that any nested functions can be queued too.
    pub fn queue_fn_and_body(&self, def: FnDefId) -> Option<TermId> {
        let (ty, def_body) = def.map(|def| (def.ty, def.body));
        // @@Todo: in the future, we might want to have a special flag by the
        // typechecker as to whether to lower something or not, rather than always
        // not lowering pure functions.
        //
        // Also, we don't queue polymorphic functions here as this doesn't
        // have any concrete types to lower to. Instead we queue all call site
        // instances of the function for lowering, this isn't ideal but it less
        // complicated than dealing with the polymorphic functions later on.
        if ty.pure || ty.implicit {
            return None;
        }

        let is_foreign = attr_store().node_has_attr(def.node_id_ensured(), attrs::FOREIGN);

        // Check that the body is marked as "foreign" since
        // we don't want to lower it.
        if is_foreign {
            None
        } else {
            Some(def_body)
        }
    }

    /// Discover all TIR runtime functions in the sources, in order to lower
    /// them to IR.
    pub fn discover_fns(&self) -> DiscoveredFns {
        let mut fns = DiscoveredFns::new();

        tir_stores().mod_def().for_each_entry(|def| {
            // Check if we can skip this module as it may of already been queued before
            // during some other pipeline run.
            //
            // @@Incomplete: mod-blocks that are already lowered won't be caught by
            // the queue-deduplication.
            match def.borrow().kind {
                ModKind::Source(id) if !self.stage_info.get(id).is_lowered() => {}
                _ => return,
            };

            for member in def.borrow().members.iter() {
                match member.borrow().value {
                    ModMemberValue::Mod(_) => {
                        // Will be handled later in the loop
                    }
                    ModMemberValue::Data(_) => {
                        // We don't need to discover anything in data types
                    }
                    ModMemberValue::Fn(def) if !fns.contains(def) => {
                        if let Some(body) = self.queue_fn_and_body(def) {
                            fns.add_fn(def);

                            // Add all nested functions too
                            let inferred_body = tir_stores().atom_info().get_inferred_value(body);
                            self.add_all_child_fns(inferred_body, &mut fns);
                        }
                    }
                    ModMemberValue::Fn(_) => {
                        // We've already found this one.
                    }
                    ModMemberValue::Intrinsic(_) => {
                        // No need to queue intrinsics, they are dealt with as
                        // they are encountered.
                    }
                }
            }
        });

        fns
    }

    /// Add all the child functions of the given term to the given set of
    /// discovered functions.
    ///
    /// *Invariant*: The term must be inferred, i.e.
    /// `self.get_inferred_value(term) = term`
    fn add_all_child_fns(&self, term: TermId, fns: &mut DiscoveredFns) {
        Visitor::new().visit(term, &mut |atom: Atom| match atom {
            Atom::Term(_) => ControlFlow::Continue(()),
            Atom::FnDef(fn_def) => {
                // @@Todo: this doesn't deal with captures.
                if !fns.contains(fn_def) && self.queue_fn_and_body(fn_def).is_some() {
                    fns.add_fn(fn_def);

                    ControlFlow::Continue(())
                } else {
                    ControlFlow::Break(())
                }
            }
            Atom::Pat(_) => ControlFlow::Continue(()),
        });
    }
}
