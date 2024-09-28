use hash_tir::tir::{CallTerm, Meta, NodeId, NodeOrigin, SymbolId, Term, TermId};

use crate::{env::TcEnv, tc::Tc};

impl<E: TcEnv> Tc<'_, E> {
    pub fn fresh_meta(&self, origin: NodeOrigin) -> TermId {
        let vars = self.substituter().get_vars_in_current_scope();
        let meta = Term::from(Meta::Generated(SymbolId::fresh_prefixed("m", origin)), origin);
        Term::from(CallTerm { implicit: false, subject: meta, args: vars }, NodeOrigin::Generated)
    }

    pub fn fresh_meta_for(&self, originating: impl NodeId) -> TermId {
        let origin = originating.origin().inferred();
        self.fresh_meta(origin)
    }
}
