//! Operations for normalising terms and types.
use derive_more::{Constructor, Deref};
use hash_tir::new::{
    terms::{Term, TermId},
    utils::common::CommonUtils,
};

use crate::{errors::TcResult, AccessToTypechecking};

#[derive(Constructor, Deref)]
pub struct NormalisationOps<'a, T: AccessToTypechecking>(&'a T);

/// Represents a normalised atom, with some additional information.
pub struct Norm<T> {
    /// The normalised term.
    pub term: T,
}

impl<T: AccessToTypechecking> NormalisationOps<'_, T> {
    /// Turn a term to weak head normal form.
    pub fn weak_head_normalise_term(&self, term_id: TermId) -> TcResult<Norm<TermId>> {
        let term = self.get_term(term_id);
        match term {
            Term::Tuple(_) => todo!(),
            Term::Prim(_) => todo!(),
            Term::Ctor(_) => todo!(),
            Term::FnCall(_) => todo!(),
            Term::FnRef(_) => todo!(),
            Term::Block(_) => todo!(),
            Term::Var(_) => todo!(),
            Term::Loop(_) => todo!(),
            Term::LoopControl(_) => todo!(),
            Term::Match(_) => todo!(),
            Term::Return(_) => todo!(),
            Term::Decl(_) => todo!(),
            Term::Assign(_) => todo!(),
            Term::Unsafe(_) => todo!(),
            Term::Access(_) => todo!(),
            Term::Cast(_) => todo!(),
            Term::TypeOf(_) => todo!(),
            Term::Ty(_) => todo!(),
            Term::Ref(_) => todo!(),
            Term::Deref(_) => todo!(),
            Term::Hole(_) => todo!(),
        }
    }

    /// Turn a term to weak head normal form, or return `None` .
    pub fn normalise_term(&self, _term_id: TermId) -> TcResult<Norm<T>> {
        todo!()
    }

    /// Reduce a term to normal form.
    pub fn potentially_normalise_term(&self, _term_id: TermId) -> TcResult<Option<TermId>> {
        todo!()
    }
}
