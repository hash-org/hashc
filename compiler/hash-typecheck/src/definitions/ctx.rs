use std::ops::ControlFlow;

use hash_source::identifier::Identifier;
use hash_tir::{
    pats::PatId,
    scopes::{StackMember, StackMemberId},
    sub::Sub,
    symbols::Symbol,
    terms::TermId,
    tys::{Ty, TyId},
};

use super::TypeableId;
use crate::errors::TcResult;

pub struct Equality {
    pub left: TypeableId,
    pub right: TypeableId,
    pub left_ty: TyId,
    pub right_ty: TyId,
}

pub struct Typing {
    pub left: TypeableId,
    pub right: TyId,
}

pub enum Judgement {
    Equality(Equality),
    Typing(Typing),
    StackMember(StackMemberId),
}
pub struct Ctx;
impl Ctx {
    fn merge_with(&mut self, other: &Self) -> &mut Self {
        todo!()
    }

    fn lookup_typing_by_name(&self, name: Symbol) -> Option<TyId> {
        todo!()
    }

    fn lookup_equality_by_name(&self, name: Symbol) -> Option<Equality> {
        todo!()
    }

    fn substitute_in_place(&mut self, sub: &Sub) {
        todo!()
    }

    fn search_typing<T>(
        &self,
        typeable: impl Into<TypeableId>,
        on_found: impl FnMut(&Typing) -> TcResult<ControlFlow<T>>,
    ) -> TcResult<Option<T>> {
        todo!()
    }

    fn search_equality<T>(
        &self,
        typeable: impl Into<TypeableId>,
        on_found: impl FnMut(&Equality) -> TcResult<ControlFlow<T>>,
    ) -> TcResult<Option<T>> {
        todo!()
    }

    fn iter_equalities<T>(
        &self,
        mut on_found: impl FnMut(&Equality) -> TcResult<ControlFlow<T>>,
    ) -> TcResult<Option<T>> {
        self.iter_judgements(|judgement| match judgement {
            Judgement::Equality(equality) => on_found(equality),
            _ => Ok(ControlFlow::Continue(())),
        })
    }

    fn iter_typings<T>(
        &self,
        mut on_found: impl FnMut(&Typing) -> TcResult<ControlFlow<T>>,
    ) -> TcResult<Option<T>> {
        self.iter_judgements(|judgement| match judgement {
            Judgement::Typing(typing) => on_found(typing),
            _ => Ok(ControlFlow::Continue(())),
        })
    }

    fn iter_judgements<T>(
        &self,
        on_found: impl FnMut(&Judgement) -> TcResult<ControlFlow<T>>,
    ) -> TcResult<Option<T>> {
        todo!()
    }

    fn iter_judgements_mut<T>(
        &self,
        on_found: impl FnMut(&mut Judgement) -> TcResult<ControlFlow<T>>,
    ) -> TcResult<Option<T>> {
        todo!()
    }

    fn add_judgement(&mut self, judgement: Judgement) -> TcResult<()> {
        todo!()
    }
}
