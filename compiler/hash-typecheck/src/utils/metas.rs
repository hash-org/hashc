use std::borrow::{Borrow, BorrowMut};

use hash_storage::store::{
    statics::SingleStoreValue, DefaultPartialStore, PartialCloneStore, PartialStore,
};
use hash_tir::{
    context::HasContext,
    tir::{
        CallTerm, FnDef, FnDefId, FnTy, Meta, Node, NodeId, NodeOrigin, SymbolId, Term, TermId,
        TyId,
    },
};

use crate::{env::TcEnv, tc::Tc};

pub struct MetaContext {
    pub(crate) metas: DefaultPartialStore<Meta, TermId>, // Contains closed terms!
}

impl MetaContext {
    pub fn new() -> Self {
        Self { metas: DefaultPartialStore::new() }
    }
}

impl<E: TcEnv> Tc<'_, E> {
    pub fn get_meta(&self, meta: Meta) -> Option<TermId> {
        self.meta_context.metas.get(meta)
    }

    pub fn fresh_meta(&self, origin: NodeOrigin) -> TermId {
        let vars = self.substituter().get_vars_in_current_scope();
        let meta = Term::from(Meta::Generated(SymbolId::fresh_prefixed("m", origin)), origin);
        Term::from(CallTerm { implicit: false, subject: meta, args: vars }, NodeOrigin::Generated)
    }

    pub fn fresh_meta_for(&self, originating: impl NodeId) -> TermId {
        let origin = originating.origin().inferred();
        self.fresh_meta(origin)
    }

    pub fn solve_meta(&self, meta: Meta, term: TermId) -> Option<TermId> {
        self.meta_context.metas.insert(meta, term)
    }
}
