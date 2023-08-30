//! Operations for unifying types and terms.

use std::{cell::Cell, collections::HashSet};

use derive_more::Deref;
use hash_storage::store::{statics::StoreId, SequenceStoreKey, TrivialSequenceStoreKey};
use hash_tir::{
    args::ArgsId,
    context::ScopeKind,
    data::DataDefCtors,
    fns::{FnCallTerm, FnTy},
    holes::Hole,
    lits::Lit,
    params::ParamsId,
    sub::Sub,
    symbols::Symbol,
    terms::{Term, TermId},
    tys::{Ty, TyId},
    utils::traversing::Atom,
};
use once_cell::unsync::OnceCell;

use crate::{
    errors::{TcError, TcResult},
    AccessToTypechecking,
};

#[derive(Deref)]
pub struct UnificationOps<'a, T: AccessToTypechecking> {
    #[deref]
    env: &'a T,
    add_to_ctx: Cell<bool>,
    modify_terms: Cell<bool>,
    pat_binds: OnceCell<HashSet<Symbol>>,
}

impl<'tc, T: AccessToTypechecking> UnificationOps<'tc, T> {
    pub fn new(env: &'tc T) -> Self {
        Self {
            env,
            add_to_ctx: Cell::new(true),
            modify_terms: Cell::new(true),
            pat_binds: OnceCell::new(),
        }
    }

    /// Disable modifying terms
    pub fn with_no_modify(&self) -> &Self {
        self.modify_terms.set(false);
        self
    }

    /// Disable adding unifications to the context.
    pub fn with_binds(&self, binds: HashSet<Symbol>) -> &Self {
        self.pat_binds.set(binds).unwrap();
        self
    }

    /// Disable adding unifications to the context.
    pub fn with_no_ctx(&self) -> &Self {
        self.add_to_ctx.set(false);
        self
    }

    /// Unify two atoms.
    pub fn unify_atoms(&self, src: Atom, target: Atom) -> TcResult<()> {
        match (src, target) {
            (Atom::Ty(src_id), Atom::Ty(target_id)) => {
                self.unify_tys(src_id, target_id)?;
                Ok(())
            }
            (Atom::Term(src_id), Atom::Term(target_id)) => {
                self.unify_terms(src_id, target_id)?;
                Ok(())
            }
            (Atom::Pat(_src_id), Atom::Pat(_target_id)) => {
                // self.unify_pats(src_id, target_id)?;
                Ok(())
            }
            _ => panic!("unify_atoms: mismatching atoms"),
        }
    }

    /// Add the given substitutions to the context.
    pub fn add_unification_from_sub(&self, sub: &Sub) {
        if self.add_to_ctx.get() {
            self.context().add_sub_to_scope(sub);
        }
    }

    /// Add the given unification to the context, and create a substitution
    /// from it.
    pub fn add_unification(&self, src: Symbol, target: impl Into<Atom>) -> Sub {
        let sub = Sub::from_pairs([(src, self.norm_ops().to_term(target.into()))]);
        self.add_unification_from_sub(&sub);
        sub
    }

    /// Emit an error that the unification cannot continue because it is
    /// blocked.
    pub fn blocked<U>(&self, src_id: impl Into<Atom>, target_id: impl Into<Atom>) -> TcResult<U> {
        Err(TcError::NeedMoreTypeAnnotationsToUnify {
            src: src_id.into(),
            target: target_id.into(),
        })
    }

    /// Emit an error that the two atoms are mismatching if `cond` is false,
    pub fn ok_or_mismatching_atoms(
        &self,
        cond: bool,
        src_id: impl Into<Atom>,
        target_id: impl Into<Atom>,
    ) -> TcResult<()> {
        if cond {
            Ok(())
        } else {
            match (src_id.into(), target_id.into()) {
                (Atom::Term(a), Atom::Term(b)) => Err(TcError::UndecidableEquality { a, b }),
                (Atom::Ty(a), Atom::Ty(b)) => {
                    Err(TcError::MismatchingTypes { expected: b, actual: a, inferred_from: None })
                }
                (Atom::FnDef(a), Atom::FnDef(b)) => Err(TcError::MismatchingFns { a, b }),
                (Atom::Pat(a), Atom::Pat(b)) => Err(TcError::MismatchingPats { a, b }),
                _ => unreachable!(),
            }
        }
    }

    /// Emit an error that the two atoms are mismatching.
    pub fn mismatching_atoms<U>(
        &self,
        src_id: impl Into<Atom>,
        target_id: impl Into<Atom>,
    ) -> TcResult<U> {
        match (src_id.into(), target_id.into()) {
            (Atom::Term(a), Atom::Term(b)) => Err(TcError::UndecidableEquality { a, b }),
            (Atom::Ty(a), Atom::Ty(b)) => {
                Err(TcError::MismatchingTypes { expected: b, actual: a, inferred_from: None })
            }
            (Atom::FnDef(a), Atom::FnDef(b)) => Err(TcError::MismatchingFns { a, b }),
            (Atom::Pat(a), Atom::Pat(b)) => Err(TcError::MismatchingPats { a, b }),
            _ => unreachable!(),
        }
    }

    /// Unify two function types.
    pub fn unify_fn_tys(
        &self,
        mut f1: FnTy,
        mut f2: FnTy,
        src_id: TyId,
        target_id: TyId,
    ) -> TcResult<()> {
        if !self.fn_modalities_match(f1, f2) {
            self.mismatching_atoms(src_id, target_id)
        } else {
            // Unify parameters and apply to return types
            self.unify_params(f1.params, f2.params, || self.unify_tys(f1.return_ty, f2.return_ty))?;

            let forward_sub = self.sub_ops().create_sub_from_param_names(f1.params, f2.params);
            f2.return_ty = self.sub_ops().apply_sub_to_ty(f2.return_ty, &forward_sub);

            let backward_sub = self.sub_ops().create_sub_from_param_names(f2.params, f1.params);
            f1.return_ty = self.sub_ops().apply_sub_to_ty(f1.return_ty, &backward_sub);

            src_id.set(src_id.value().with_data(f1.into()));
            target_id.set(target_id.value().with_data(f2.into()));

            Ok(())
        }
    }

    /// Unify two holes.
    ///
    /// This modifies src to have the contents of dest, and adds a unification
    /// to the context.
    pub fn unify_hole_with(
        &self,
        hole_src: impl Into<Atom>,
        sub_dest: impl Into<Atom>,
    ) -> TcResult<()> {
        let norm_ops = self.norm_ops();
        let hole_atom: Atom = hole_src.into();
        let sub_dest_atom: Atom = sub_dest.into();

        let hole_symbol = match hole_atom {
            Atom::Term(term_id) => {
                let dest_term = (norm_ops.to_term(sub_dest_atom)).value();
                match *term_id.value() {
                    Term::Hole(Hole(h)) => {
                        if self.modify_terms.get() {
                            term_id.set(dest_term);
                        }
                        h
                    }
                    _ => panic!("unify_hole_with: expected hole for hole src"),
                }
            }
            Atom::Ty(ty_id) => {
                let dest_ty = norm_ops.to_ty(sub_dest_atom).value();
                match *ty_id.value() {
                    Ty::Hole(Hole(h)) => {
                        if self.modify_terms.get() {
                            ty_id.set(dest_ty);
                        }
                        h
                    }
                    _ => panic!("unify_hole_with: expected hole for hole src"),
                }
            }
            Atom::FnDef(_) | Atom::Pat(_) => {
                panic!("unify_hole_with: expected term or ty for hole src")
            }
        };
        self.add_unification(hole_symbol, sub_dest_atom);
        Ok(())
    }

    /// Unify two holes.
    pub fn unify_holes(
        &self,
        h1: Hole,
        h2: Hole,
        src_id: impl Into<Atom>,
        target_id: impl Into<Atom>,
    ) -> TcResult<()> {
        if h1 == h2 {
            Ok(())
        } else {
            // We can't unify two holes, so we have to block
            self.blocked(src_id, target_id)
        }
    }

    pub fn unify_tys_self_contained(&self, src_id: TyId, target_id: TyId) -> TcResult<(TyId, Sub)> {
        let initial = target_id;
        let sub = self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
            self.unify_tys(src_id, target_id)?;
            Ok(self.sub_ops().create_sub_from_current_scope())
        })?;
        let subbed_initial = self.sub_ops().apply_sub_to_ty(initial, &sub);
        self.add_unification_from_sub(&sub);
        Ok((subbed_initial, sub))
    }

    pub fn unify_vars(&self, a: Symbol, b: Symbol, a_id: TermId, b_id: TermId) -> TcResult<()> {
        if let Some(binds) = self.pat_binds.get() {
            if binds.contains(&a) {
                self.add_unification(b, a_id);
                return Ok(());
            }
            if binds.contains(&b) {
                self.add_unification(a, b_id);
                return Ok(());
            }
        }
        if a == b {
            Ok(())
        } else {
            self.mismatching_atoms(a_id, b_id)
        }
    }

    /// Unify two types.
    pub fn unify_tys(&self, src_id: TyId, target_id: TyId) -> TcResult<()> {
        if src_id == target_id {
            return Ok(());
        }

        let norm_ops = self.norm_ops();

        norm_ops.normalise_in_place(src_id.into())?;
        norm_ops.normalise_in_place(target_id.into())?;

        let src = src_id.value();
        let target = target_id.value();

        match (*src, *target) {
            (Ty::Hole(h1), Ty::Hole(h2)) => self.unify_holes(h1, h2, src_id, target_id),
            (Ty::Hole(_a), _) => self.unify_hole_with(src_id, target_id),
            (_, Ty::Hole(_b)) => self.unify_hole_with(target_id, src_id),

            (Ty::Var(a), _) if self.pat_binds.get().is_some() => {
                self.add_unification(a, target_id.as_term());
                Ok(())
            }
            (_, Ty::Var(b)) if self.pat_binds.get().is_some() => {
                self.add_unification(b, src_id.as_term());
                Ok(())
            }

            // If the source is uninhabitable, then we can unify it with
            // anything
            (_, _) if self.is_uninhabitable(src_id)? => Ok(()),

            (Ty::Var(a), Ty::Var(b)) => {
                self.unify_vars(a, b, src_id.as_term(), target_id.as_term())
            }
            (Ty::Var(_), _) | (_, Ty::Var(_)) => self.mismatching_atoms(src_id, target_id),

            (Ty::Eval(t1), Ty::Eval(t2)) => self.unify_terms(t1, t2),
            (Ty::Eval(_), _) | (_, Ty::Eval(_)) => self.mismatching_atoms(src_id, target_id),

            (Ty::Tuple(t1), Ty::Tuple(t2)) => self.unify_params(t1.data, t2.data, || Ok(())),
            (Ty::Tuple(_), _) | (_, Ty::Tuple(_)) => self.mismatching_atoms(src_id, target_id),

            (Ty::Fn(f1), Ty::Fn(f2)) => self.unify_fn_tys(f1, f2, src_id, target_id),
            (Ty::Fn(_), _) | (_, Ty::Fn(_)) => self.mismatching_atoms(src_id, target_id),

            (Ty::Ref(r1), Ty::Ref(r2)) if r1.mutable == r2.mutable && r1.kind == r2.kind => {
                self.unify_tys(r1.ty, r2.ty)
            }
            (Ty::Ref(_), _) | (_, Ty::Ref(_)) => self.mismatching_atoms(src_id, target_id),

            (Ty::Data(d1), Ty::Data(d2)) if d1.data_def == d2.data_def => {
                self.unify_args(d1.args, d2.args)
            }
            (Ty::Data(_), _) | (_, Ty::Data(_)) => self.mismatching_atoms(src_id, target_id),

            (Ty::Universe(u1), Ty::Universe(u2)) => self.ok_or_mismatching_atoms(
                u1.size.is_none() || u2.size.is_none() || u1.size.unwrap() <= u2.size.unwrap(),
                src_id,
                target_id,
            ),
        }
    }

    /// Whether two literals are equal.
    pub fn lits_are_equal(&self, src: Lit, target: Lit) -> bool {
        match (src, target) {
            (Lit::Int(i1), Lit::Int(i2)) => i1.value() == i2.value(),
            (Lit::Str(s1), Lit::Str(s2)) => s1.value() == s2.value(),
            (Lit::Char(c1), Lit::Char(c2)) => c1.value() == c2.value(),
            (Lit::Float(f1), Lit::Float(f2)) => f1.value() == f2.value(),
            _ => false,
        }
    }

    pub fn unify_fn_calls(&self, src: FnCallTerm, target: FnCallTerm) -> TcResult<()> {
        self.unify_terms(src.subject, target.subject)?;
        self.unify_args(src.args, target.args)?;
        Ok(())
    }

    /// Unify two terms.
    ///
    /// Unless these are types, they must be definitionally (up to beta
    /// reduction) equal.
    pub fn unify_terms(&self, src_id: TermId, target_id: TermId) -> TcResult<()> {
        if src_id == target_id {
            return Ok(());
        }

        let norm_ops = self.norm_ops();

        norm_ops.normalise_in_place(src_id.into())?;
        norm_ops.normalise_in_place(target_id.into())?;

        let src = src_id.value();
        let target = target_id.value();

        match (src_id.try_as_ty(), target_id.try_as_ty()) {
            (Some(src_ty), Some(target_ty)) => self.unify_tys(src_ty, target_ty),
            _ => match (*src, *target) {
                (Term::Hole(h1), Term::Hole(h2)) => self.unify_holes(h1, h2, src_id, target_id),
                (Term::Hole(_a), _) => self.unify_hole_with(src_id, target_id),
                (_, Term::Hole(_b)) => self.unify_hole_with(target_id, src_id),

                (Term::Var(a), _) if self.pat_binds.get().is_some() => {
                    self.add_unification(a, target_id);
                    Ok(())
                }
                (_, Term::Var(b)) if self.pat_binds.get().is_some() => {
                    self.add_unification(b, src_id);
                    Ok(())
                }
                (Term::Var(a), Term::Var(b)) => self.unify_vars(a, b, src_id, target_id),
                (Term::Var(_), _) | (_, Term::Var(_)) => self.mismatching_atoms(src_id, target_id),

                (Term::Tuple(t1), Term::Tuple(t2)) => self.unify_args(t1.data, t2.data),
                (Term::Tuple(_), _) | (_, Term::Tuple(_)) => {
                    self.mismatching_atoms(src_id, target_id)
                }

                (Term::Ctor(c1), Term::Ctor(c2)) if c1.ctor == c2.ctor => {
                    self.unify_args(c1.data_args, c2.data_args)?;
                    self.unify_args(c1.ctor_args, c2.ctor_args)?;
                    Ok(())
                }
                (Term::Ctor(_), _) | (_, Term::Ctor(_)) => {
                    self.mismatching_atoms(src_id, target_id)
                }

                (Term::Ty(t1), _) => self.unify_terms(t1.as_term(), target_id),
                (_, Term::Ty(t2)) => self.unify_terms(src_id, t2.as_term()),

                (Term::Lit(l1), Term::Lit(l2)) => {
                    self.ok_or_mismatching_atoms(self.lits_are_equal(l1, l2), src_id, target_id)
                }
                (Term::Lit(_), _) | (_, Term::Lit(_)) => self.mismatching_atoms(src_id, target_id),

                (Term::Access(a1), Term::Access(a2)) if a1.field == a2.field => {
                    self.unify_terms(a1.subject, a2.subject)
                }
                (Term::Access(_), _) | (_, Term::Access(_)) => {
                    self.mismatching_atoms(src_id, target_id)
                }

                (Term::Ref(r1), Term::Ref(r2))
                    if r1.mutable == r2.mutable && r1.kind == r2.kind =>
                {
                    self.unify_terms(r1.subject, r2.subject)
                }
                (Term::Ref(_), _) | (_, Term::Ref(_)) => self.mismatching_atoms(src_id, target_id),

                (Term::FnCall(c1), Term::FnCall(c2)) => self.unify_fn_calls(c1, c2),
                (Term::FnCall(_), _) | (_, Term::FnCall(_)) => {
                    self.mismatching_atoms(src_id, target_id)
                }

                (Term::FnRef(f1), Term::FnRef(f2)) if f1 == f2 => Ok(()),
                (Term::FnRef(_), _) | (_, Term::FnRef(_)) => {
                    self.mismatching_atoms(src_id, target_id)
                }

                // @@Todo: rest
                _ => self.mismatching_atoms(src_id, target_id),
            },
        }
    }

    /// Unify two parameter lists.
    ///
    /// This takes a function to run in the scope of the parameters. It also
    /// adds the ambient substitutions to the current scope.
    ///
    /// Names are taken from dest
    pub fn unify_params<U>(
        &self,
        src_id: ParamsId,
        target_id: ParamsId,
        in_param_scope: impl FnOnce() -> TcResult<U>,
    ) -> TcResult<U> {
        // Validate the parameters and ensure they are of the same length
        self.param_ops().validate_params(src_id)?;
        self.param_ops().validate_params(target_id)?;
        if src_id.len() != target_id.len() {
            return Err(TcError::WrongParamLength {
                given_params_id: src_id,
                annotation_params_id: target_id,
            });
        }
        let forward_sub = self.sub_ops().create_sub_from_param_names(src_id, target_id);
        let backward_sub = self.sub_ops().create_sub_from_param_names(target_id, src_id);

        let (result, shadowed_sub) =
            self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
                for (src_param_id, target_param_id) in src_id.iter().zip(target_id.iter()) {
                    let src_param = src_param_id.value();
                    let target_param = target_param_id.value();

                    // Substitute the names
                    self.context().add_assignment(
                        src_param.name,
                        src_param.ty,
                        Term::from(target_param.name),
                    );

                    // Unify the types
                    self.unify_tys(src_param.ty, target_param.ty)?;
                    self.sub_ops().apply_sub_to_ty_in_place(target_param.ty, &forward_sub);
                    self.sub_ops().apply_sub_to_ty_in_place(src_param.ty, &backward_sub);
                }

                // Run the in-scope closure
                let result = in_param_scope()?;

                // Only keep the substitutions that do not refer to the parameters
                let scope_sub = self.sub_ops().create_sub_from_current_scope();
                let shadowed_sub = self
                    .sub_ops()
                    .hide_param_binds(src_id.iter().chain(target_id.iter()), &scope_sub);
                Ok((result, shadowed_sub))
            })?;

        // Add the shadowed substitutions to the ambient scope
        self.add_unification_from_sub(&shadowed_sub);

        Ok(result)
    }

    /// Unify two argument lists.
    pub fn unify_args(&self, src_id: ArgsId, target_id: ArgsId) -> TcResult<()> {
        if src_id.len() != target_id.len() {
            return Err(TcError::DifferentParamOrArgLengths {
                a: src_id.into(),
                b: target_id.into(),
            });
        }
        for (src_arg_id, target_arg_id) in src_id.iter().zip(target_id.iter()) {
            let src_arg = src_arg_id.value();
            let target_arg = target_arg_id.value();
            self.unify_terms(src_arg.value, target_arg.value)?;
        }
        Ok(())
    }

    /// Whether two function types match in terms of their modality.
    pub fn fn_modalities_match(&self, f1: FnTy, f2: FnTy) -> bool {
        f1.implicit == f2.implicit && f1.is_unsafe == f2.is_unsafe && f1.pure == f2.pure
    }

    /// Determine whether two terms are equal.
    pub fn terms_are_equal(&self, t1: TermId, t2: TermId) -> bool {
        // @@Todo: prevent modification?
        let uni_ops = self.uni_ops();
        uni_ops.with_no_modify();
        self.context().enter_scope(ScopeKind::Sub, || uni_ops.unify_terms(t1, t2).is_ok())
    }

    /// Determine whether the given type is uninhabitable.
    ///
    /// This does not look too deeply into the type, so it may return false
    /// for types that are actually uninhabitable.
    pub fn is_uninhabitable(&self, ty: TyId) -> TcResult<bool> {
        let ty = self.norm_ops().to_ty(self.norm_ops().normalise(ty.into())?);
        match *ty.value() {
            Ty::Data(data_ty) => {
                let data_def = data_ty.data_def.borrow();
                match data_def.ctors {
                    DataDefCtors::Defined(ctors) => Ok(ctors.value().len() == 0),
                    DataDefCtors::Primitive(_) => Ok(false),
                }
            }
            _ => Ok(false),
        }
    }
}
