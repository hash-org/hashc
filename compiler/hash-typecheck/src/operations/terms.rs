use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    tir::{ArgsId, BindingPat, NodesId, Pat, Term, TermId, Ty, TyId, VarTerm},
    visitor::{Atom, Map, Visitor},
};

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{already_normalised, NormaliseResult},
    tc::{FnInferMode, Tc},
    traits::{OperationsOn, OperationsOnNode},
    utils::dumping::potentially_dump_tir,
};

impl<E: TcEnv> Tc<'_, E> {
    /// Infer the given arguments as one type.
    ///
    /// Returns the inferred list, and its inferred type.
    pub fn check_unified_args(&self, args: ArgsId, element_annotation_ty: TyId) -> TcResult<()> {
        for item in args.elements().value() {
            self.check_node(item.data.value, element_annotation_ty)?;
        }
        Ok(())
    }
}

impl<E: TcEnv> OperationsOnNode<TermId> for Tc<'_, E> {
    type AnnotNode = TyId;

    fn check_node(&self, term_id: TermId, annotation_ty: Self::AnnotNode) -> TcResult<()> {
        self.register_new_atom(term_id, annotation_ty);
        match *term_id.value() {
            Term::Tuple(mut tuple_term) => self.check(&mut tuple_term, annotation_ty, term_id)?,
            Term::Lit(lit_term) => self.check_node(lit_term, annotation_ty)?,
            Term::Array(mut prim_term) => { self.check(&mut prim_term, annotation_ty, term_id) }?,
            Term::Ctor(mut ctor_term) => self.check(&mut ctor_term, annotation_ty, term_id)?,
            Term::Call(mut call_term) => self.check(&mut call_term, annotation_ty, term_id)?,
            Term::Fn(mut fn_def_id) => self
                .fn_infer_mode
                .enter(FnInferMode::Body, || self.check(&mut fn_def_id, annotation_ty, term_id))?,
            Term::Var(mut var_term) => self.check(&mut var_term, annotation_ty, term_id)?,
            Term::Return(mut return_term) => {
                self.check(&mut return_term, annotation_ty, term_id)?
            }
            Term::Deref(mut deref_term) => self.check(&mut deref_term, annotation_ty, term_id)?,
            Term::LoopControl(mut loop_control_term) => {
                self.check(&mut loop_control_term, annotation_ty, term_id)?
            }
            Term::Unsafe(mut unsafe_term) => {
                self.check(&mut unsafe_term, annotation_ty, term_id)?
            }
            Term::Loop(mut loop_term) => self.check(&mut loop_term, annotation_ty, term_id)?,
            Term::Block(mut block_term) => self.check(&mut block_term, annotation_ty, term_id)?,
            Term::TyOf(mut ty_of_term) => self.check(&mut ty_of_term, annotation_ty, term_id)?,
            Term::Ref(mut ref_term) => self.check(&mut ref_term, annotation_ty, term_id)?,
            Term::Annot(mut cast_term) => self.check(&mut cast_term, annotation_ty, term_id)?,
            Term::Access(mut access_term) => {
                self.check(&mut access_term, annotation_ty, term_id)?
            }
            Term::Index(mut index_term) => self.check(&mut index_term, annotation_ty, term_id)?,
            Term::Match(mut match_term) => self.check(&mut match_term, annotation_ty, term_id)?,
            Term::Assign(mut assign_term) => {
                self.check(&mut assign_term, annotation_ty, term_id)?
            }
            Term::Intrinsic(mut intrinsic) => self.check(&mut intrinsic, annotation_ty, term_id)?,
            Term::Hole(mut hole) => self.check(&mut hole, annotation_ty, term_id)?,
            Ty::TupleTy(mut tuple_ty) => self.check(&mut tuple_ty, annotation_ty, term_id)?,
            Ty::FnTy(mut fn_ty) => self.check(&mut fn_ty, annotation_ty, term_id)?,
            Ty::RefTy(mut ref_ty) => {
                self.check(&mut ref_ty, annotation_ty, term_id)?;
            }
            Ty::DataTy(mut data_ty) => {
                self.check(&mut data_ty, annotation_ty, term_id)?;
            }
            Ty::Universe(mut universe_ty) => {
                self.check(&mut universe_ty, annotation_ty, term_id)?
            }
            Term::Pat(pat) => match pat {
                Pat::Binding(mut var) => self.check(&mut var, annotation_ty, term_id)?,
                Pat::Range(mut range_pat) => self.check(&mut range_pat, annotation_ty, term_id)?,
                Pat::Or(mut or_pat) => self.check(&mut or_pat, annotation_ty, term_id)?,
                Pat::If(mut if_pat) => self.check(&mut if_pat, annotation_ty, term_id)?,
                Pat::Spread(_) => (), // @@Todo: handle
            },
        };

        self.check_ty(annotation_ty)?;
        self.register_atom_inference(term_id, term_id, annotation_ty);

        // Potentially evaluate the term.
        self.potentially_run_expr(term_id, annotation_ty)?;
        potentially_dump_tir(term_id);

        Ok(())
    }

    fn unify_nodes(&self, src_id: TermId, target_id: TermId) -> TcResult<()> {
        if src_id == target_id {
            return Ok(());
        }

        // Substitute from context
        let v = Visitor::new();
        let src_id_subbed = v.copy(src_id);
        self.substituter().apply_sub_from_context(src_id_subbed);
        let target_id_subbed = v.copy(target_id);
        self.substituter().apply_sub_from_context(target_id_subbed);
        let src = src_id_subbed.value().data;
        let target = target_id_subbed.value().data;

        match (src, target) {
            (Term::Hole(mut h1), Term::Hole(mut h2)) => {
                self.unify(&mut h1, &mut h2, src_id, target_id)
            }
            (Term::Hole(a), _) => self.unify_hole_with(a, src_id, target_id),
            (_, Term::Hole(b)) => self.unify_hole_with(b, target_id, src_id),
            (
                Term::Var(VarTerm { symbol: a })
                | Term::Pat(Pat::Binding(BindingPat { name: a, .. })),
                Term::Var(VarTerm { symbol: b })
                | Term::Pat(Pat::Binding(BindingPat { name: b, .. })),
            ) if a == b => Ok(()),
            (Term::Var(a), _) => self.unify_var_with(a, src_id, target_id),
            (_, Term::Var(b)) => self.unify_var_with(b, target_id, src_id),
            (Term::Pat(Pat::Binding(a)), _) => self.unify_binding_with(a, target_id),
            (_, Term::Pat(Pat::Binding(b))) => self.unify_binding_with(b, src_id),

            // If the source is uninhabitable, then we can unify it with
            // anything
            (_, _) if self.is_uninhabitable(src_id)? => Ok(()),

            (Ty::TupleTy(mut t1), Ty::TupleTy(mut t2)) => {
                self.unify(&mut t1, &mut t2, src_id, target_id)
            }
            (Ty::FnTy(mut f1), Ty::FnTy(mut f2)) => self.unify(&mut f1, &mut f2, src_id, target_id),
            (Ty::RefTy(mut r1), Ty::RefTy(mut r2)) => {
                self.unify(&mut r1, &mut r2, src_id, target_id)
            }
            (Ty::DataTy(mut d1), Ty::DataTy(mut d2)) => {
                self.unify(&mut d1, &mut d2, src_id, target_id)
            }
            (Ty::Universe(mut u1), Ty::Universe(mut u2)) => {
                self.unify(&mut u1, &mut u2, src_id, target_id)
            }
            (Term::Tuple(mut t1), Term::Tuple(mut t2)) => {
                self.unify(&mut t1, &mut t2, src_id, target_id)
            }
            (Term::Ctor(mut c1), Term::Ctor(mut c2)) => {
                self.unify(&mut c1, &mut c2, src_id, target_id)
            }
            (Term::Lit(l1), Term::Lit(l2)) => self.unify_nodes(l1, l2),
            (Term::Fn(mut f1), Term::Fn(mut f2)) => self.unify(&mut f1, &mut f2, src_id, target_id),
            (Term::Call(mut c1), Term::Call(mut c2)) => self
                .unify(&mut c1, &mut c2, src_id, target_id)
                .or_else(|_| self.normalise_and_unify_nodes(src_id, target_id)),
            (Term::Access(mut a1), Term::Access(mut a2)) => self
                .unify(&mut a1, &mut a2, src_id, target_id)
                .or_else(|_| self.normalise_and_unify_nodes(src_id, target_id)),
            (Term::Ref(mut r1), Term::Ref(mut r2)) => self
                .unify(&mut r1, &mut r2, src_id, target_id)
                .or_else(|_| self.normalise_and_unify_nodes(src_id, target_id)),
            (Term::Index(mut i1), Term::Index(mut i2)) => self
                .unify(&mut i1, &mut i2, src_id, target_id)
                .or_else(|_| self.normalise_and_unify_nodes(src_id, target_id)),
            (Term::Match(mut m1), Term::Match(mut m2)) => {
                self.unify(&mut m1, &mut m2, src_id, target_id)
            }
            (Term::Assign(mut a1), Term::Assign(mut a2)) => {
                self.unify(&mut a1, &mut a2, src_id, target_id)
            }
            (Term::Return(mut r1), Term::Return(mut r2)) => {
                self.unify(&mut r1, &mut r2, src_id, target_id)
            }
            (Term::Block(mut b1), Term::Block(mut b2)) => {
                self.unify(&mut b1, &mut b2, src_id, target_id)
            }
            (Term::Loop(mut l1), Term::Loop(mut l2)) => {
                self.unify(&mut l1, &mut l2, src_id, target_id)
            }
            (Term::LoopControl(mut l1), Term::LoopControl(mut l2)) => {
                self.unify(&mut l1, &mut l2, src_id, target_id)
            }
            (Term::Deref(mut d1), Term::Deref(mut d2)) => {
                self.unify(&mut d1, &mut d2, src_id, target_id)
            }
            (Term::Unsafe(mut u1), Term::Unsafe(mut u2)) => {
                self.unify(&mut u1, &mut u2, src_id, target_id)
            }
            (Term::TyOf(mut t1), Term::TyOf(mut t2)) => {
                self.unify(&mut t1, &mut t2, src_id, target_id)
            }
            (Term::Annot(mut a1), Term::Annot(mut a2)) => {
                self.unify(&mut a1, &mut a2, src_id, target_id)
            }
            (Term::Intrinsic(mut i1), Term::Intrinsic(mut i2)) => {
                self.unify(&mut i1, &mut i2, src_id, target_id)
            }
            (Term::Pat(Pat::If(mut i1)), Term::Pat(Pat::If(mut i2))) => {
                self.unify(&mut i1, &mut i2, src_id, target_id)
            }
            (Term::Pat(Pat::Or(mut o1)), Term::Pat(Pat::Or(mut o2))) => {
                self.unify(&mut o1, &mut o2, src_id, target_id)
            }
            (Term::Pat(Pat::Range(mut r1)), Term::Pat(Pat::Range(mut r2))) => {
                self.unify(&mut r1, &mut r2, src_id, target_id)
            }
            _ => self.normalise_and_unify_nodes(src_id, target_id),
        }
    }

    fn try_normalise_node(&self, term: TermId) -> NormaliseResult<ControlFlow<TermId>> {
        match *term.value() {
            Term::TyOf(ty_of_term) => self.try_normalise(ty_of_term, term),
            Term::Unsafe(unsafe_expr) => self.try_normalise(unsafe_expr, term),
            Term::Match(match_term) => self.try_normalise(match_term, term),
            Term::Call(fn_call) => self.try_normalise(fn_call, term),
            Term::Annot(cast_term) => self.try_normalise(cast_term, term),
            Term::Hole(h) => self.try_normalise(h, term),
            Term::Var(v) => self.try_normalise(v, term),
            Term::Deref(deref_term) => self.try_normalise(deref_term, term),
            Term::Access(access_term) => self.try_normalise(access_term, term),
            Term::Index(index_term) => self.try_normalise(index_term, term),

            // Introduction forms:
            Term::Ref(_)
            | Term::Intrinsic(_)
            | Term::Fn(_)
            | Term::Lit(_)
            | Term::Array(_)
            | Term::Tuple(_)
            | Term::Ctor(_) => Ok(Some(ControlFlow::Continue(()))),

            // Patterns
            Term::Pat(_pat) => already_normalised(),

            // Imperative:
            Term::LoopControl(loop_control) => self.try_normalise(loop_control, term),
            Term::Assign(assign_term) => self.try_normalise(assign_term, term),
            Term::Return(return_expr) => self.try_normalise(return_expr, term),
            Term::Block(block_term) => self.try_normalise(block_term, term),
            Term::Loop(loop_term) => self.try_normalise(loop_term, term),
            Ty::FnTy(_) | Ty::TupleTy(_) | Ty::DataTy(_) | Ty::Universe(_) | Ty::RefTy(_) => {
                Ok(Some(ControlFlow::Continue(())))
            }
        }
    }
}

impl<E: TcEnv> Tc<'_, E> {
    pub(crate) fn normalise_and_unify_nodes<N>(&self, src_id: N, target_id: N) -> TcResult<()>
    where
        N: Copy + Into<Atom>,
        Visitor: Map<N>,
        Self: OperationsOnNode<N>,
    {
        match self.potentially_normalise_node_no_signals(src_id)? {
            Some(src_id_new) => self.unify_nodes(src_id_new, target_id),
            None => match self.potentially_normalise_node_no_signals(target_id)? {
                Some(target_id_new) => self.unify_nodes(src_id, target_id_new),
                None => self.mismatching_atoms(src_id, target_id),
            },
        }
    }
}
