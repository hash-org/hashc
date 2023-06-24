pub mod ctx;

use std::ops::ControlFlow;

use hash_source::identifier::Identifier;
use hash_tir::{
    pats::PatId,
    scopes::{StackMember, StackMemberId},
    sub::Sub,
    symbols::Symbol,
    terms::{Term, TermId},
    tys::{Ty, TyId},
};

use self::ctx::Ctx;
use crate::{errors::TcResult, AccessToTypechecking, Tc};

pub enum TypeableId {
    Symbol(Symbol),
    Ty(TyId),
    Term(TermId),
    Pat(PatId),
}

trait Typeable: Clone {}

trait Type: Typeable {}

trait Norm<T: Typeable> {
    fn normalise_in_place(&self, term: &mut T, ctx: &Ctx) -> TcResult<()>;

    fn normalise_copied(&self, term: &T, ctx: &Ctx) -> TcResult<T>;
}

trait Subst<T: Typeable> {
    fn iter_free_vars<U>(
        &self,
        term: &T,
        on_found: impl FnMut(Symbol) -> TcResult<ControlFlow<U>>,
    ) -> TcResult<Option<U>>;

    fn sub_in_place(&self, term: &mut T, sub: &Sub, ctx: &Ctx) -> TcResult<()>;

    fn sub_copied(&self, term: &T, sub: &Sub, ctx: &Ctx) -> TcResult<(T, Ctx)>;
}

trait Infer<T: Typeable, Ty: Type> {
    fn infer_in_place(&self, left: &mut T, right: &mut Ty, ctx: &mut Ctx) -> TcResult<()>;
}

trait Unify<T: Typeable> {
    fn unify_in_place(
        &self,
        left: &mut T,
        right: &mut T,
        ctx: &mut Ctx,
        sub: &mut Sub,
    ) -> TcResult<()>;

    fn unify_copied(&self, left: &T, right: &T, ctx: &Ctx, sub: &Sub) -> TcResult<(T, Ctx, Sub)>;
}

impl Typeable for Ty {}

impl<'a, T: AccessToTypechecking> Unify<Ty> for Tc<'a, T> {
    fn unify_in_place(
        &self,
        left: &mut Ty,
        right: &mut Ty,
        ctx: &mut Ctx,
        sub: &mut Sub,
    ) -> TcResult<()> {
        todo!()
    }

    fn unify_copied(
        &self,
        left: &Ty,
        right: &Ty,
        ctx: &Ctx,
        sub: &Sub,
    ) -> TcResult<(Ty, Ctx, Sub)> {
        todo!()
    }
}

impl Typeable for Term {}

impl<'a, T: AccessToTypechecking> Unify<Term> for Tc<'a, T> {
    fn unify_in_place(
        &self,
        left: &mut Term,
        right: &mut Term,
        ctx: &mut Ctx,
        sub: &mut Sub,
    ) -> TcResult<()> {
        todo!()
    }

    fn unify_copied(
        &self,
        left: &Term,
        right: &Term,
        ctx: &Ctx,
        sub: &Sub,
    ) -> TcResult<(Term, Ctx, Sub)> {
        todo!()
    }
}
