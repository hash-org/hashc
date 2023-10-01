use hash_tir::{
    sub::Sub,
    tir::{SymbolId, TermId},
};

use crate::{checker::Tc, env::TcEnv};

impl<E: TcEnv> Tc<'_, E> {
    /// Add the given substitutions to the context.
    pub fn add_unification_from_sub(&self, sub: &Sub) {
        self.context().add_sub_to_scope(sub);
    }

    /// Add the given unification to the context, and create a substitution
    /// from it.
    pub fn add_unification(&self, src: SymbolId, target: TermId) -> Sub {
        let sub = Sub::from_pairs([(src, target)]);
        self.add_unification_from_sub(&sub);
        sub
    }
}
