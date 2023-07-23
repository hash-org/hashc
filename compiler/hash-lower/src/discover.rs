//! This module contains functionality to discover functions in the TIR tree in
//! order to lower them to IR.
//!
//! For now, non-pure functions are always queued for lowering.
use std::ops::ControlFlow;

use derive_more::Constructor;
use hash_pipeline::workspace::StageInfo;
use hash_source::identifier::IDENTS;
use hash_storage::store::{statics::StoreId, PartialStore, TrivialSequenceStoreKey};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    environment::{
        env::{AccessToEnv, Env},
        stores::tir_stores,
    },
    fns::{FnBody, FnDef, FnDefId},
    mods::{ModDef, ModKind, ModMemberValue},
    terms::TermId,
    utils::{traversing::Atom, AccessToUtils},
};
use indexmap::IndexSet;

use crate::ctx::BuilderCtx;

/// Discoverer for functions to lower in the TIR tree.
#[derive(Constructor)]
pub(crate) struct FnDiscoverer<'a> {
    /// The TIR environment which can be used to read information about
    /// all TIR terms and definitions.
    ctx: &'a BuilderCtx<'a>,

    /// A reference to [StageInfo] which refers to what the current
    /// status of each source is. This is used to avoid re-queuing modules
    /// that may of been queued in a previous run.
    stage_info: &'a StageInfo,
}

impl AccessToEnv for FnDiscoverer<'_> {
    fn env(&self) -> &Env {
        self.ctx.env()
    }
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

impl FnDiscoverer<'_> {
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

        // Also, we don't queue polymorphic functions here as this doesn't
        // have any concrete types to lower to. Instead we queue all call site
        // instances of the function for lowering, this isn't ideal but it less
        // complicated than dealing with the polymorphic functions later on.
        if fn_def.ty.implicit {
            return false;
        }

        match fn_def.body {
            FnBody::Defined(_) => {
                // Check that the body is marked as "foreign" since
                // we don't want to lower it.
                tir_stores().directives().map_fast(def_id.into(), |maybe_directives| {
                    if let Some(directives) = maybe_directives && directives.contains(IDENTS.foreign) {
                        false
                    } else {
                        true
                    }
                })
            }

            // Intrinsics and axioms have no effect on the IR lowering
            FnBody::Intrinsic(_) | FnBody::Axiom => false,
        }
    }

    /// Discover all TIR runtime functions in the sources, in order to lower
    /// them to IR.
    pub fn discover_fns(&self) -> DiscoveredFns {
        let mut fns = DiscoveredFns::new();

        for mod_def_id in ModDef::iter_all_mods() {
            // Check if we can skip this module as it may of already been queued before
            // during some other pipeline run.
            //
            // @@Incomplete: mod-blocks that are already lowered won't be caught by
            // the queue-deduplication.
            match mod_def_id.borrow().kind {
                ModKind::Source(id, _) if !self.stage_info.get(id).is_lowered() => {}
                _ => continue,
            };

            for member in mod_def_id.borrow().members.iter() {
                match member.borrow().value {
                    ModMemberValue::Mod(_) => {
                        // Will be handled later in the loop
                    }
                    ModMemberValue::Data(_) => {
                        // We don't need to discover anything in data types
                    }
                    ModMemberValue::Fn(fn_def_id) => {
                        let fn_def = fn_def_id.value();

                        if self.fn_needs_to_be_lowered(fn_def_id, &fn_def) {
                            fns.add_fn(fn_def_id);

                            let FnBody::Defined(body) = fn_def.body else { unreachable!() };

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
                Atom::FnDef(fn_def) => {
                    // @@Todo: this doesn't deal with captures.
                    if self.fn_needs_to_be_lowered(fn_def, &fn_def.value()) {
                        fns.add_fn(fn_def);

                        Ok(ControlFlow::Continue(()))
                    } else {
                        Ok(ControlFlow::Break(()))
                    }
                }
                Atom::Pat(_) => Ok(ControlFlow::Continue(())),
            })
            .into_ok();
    }
}
