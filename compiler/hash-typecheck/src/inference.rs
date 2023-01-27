//! Operations to infer types of terms and patterns.

use derive_more::{Constructor, Deref};
use hash_ast::ast::{FloatLitKind, IntLitKind};
use hash_intrinsics::utils::PrimitiveUtils;
use hash_reporting::diagnostic::Diagnostics;
use hash_source::constant::{FloatTy, IntTy, SIntTy, UIntTy};
use hash_tir::{
    new::{
        args::{ArgsId, PatArgsId},
        casting::CastTerm,
        control::{LoopControlTerm, LoopTerm, ReturnTerm},
        data::{CtorTerm, DataDefId, DataTy},
        defs::{DefArgsId, DefParamGroupData, DefParamsId, DefPatArgsId},
        environment::context::{BindingKind, BoundVarOrigin, ScopeKind},
        fns::{FnBody, FnCallTerm, FnDefId, FnTy},
        holes::HoleBinderKind,
        lits::{Lit, PrimTerm},
        mods::{ModDefId, ModMember, ModMemberValue},
        params::{ParamData, ParamsId},
        pats::{Pat, PatId},
        refs::{DerefTerm, RefTerm, RefTy},
        scopes::BlockTerm,
        symbols::Symbol,
        terms::{RuntimeTerm, Term, TermId, UnsafeTerm},
        tuples::{TupleTerm, TupleTy},
        tys::{Ty, TyId, TypeOfTerm},
        utils::{common::CommonUtils, AccessToUtils},
    },
    ty_as_variant,
};
use hash_utils::store::{CloneStore, SequenceStore, Store};

use super::unification::Unification;
use crate::{
    errors::{TcError, TcResult},
    AccessToTypechecking,
};

#[derive(Constructor, Deref)]
pub struct InferenceOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> InferenceOps<'_, T> {
    /// Infer the given generic definition arguments (specialised for args and
    /// pat args below)
    pub fn infer_some_def_args<DefArgGroup>(
        &self,
        def_args: &[DefArgGroup],
        infer_def_arg_group: impl Fn(&DefArgGroup) -> TcResult<DefParamGroupData>,
    ) -> TcResult<DefParamsId> {
        // @@Todo: dependent definition parameters
        let mut def_params = vec![];
        let mut has_error = false;

        for group in def_args {
            match self.try_or_add_error(infer_def_arg_group(group)) {
                // Type was inferred
                Some(group) => def_params.push(group),
                // Error occurred
                None => has_error = true,
            }
        }

        if has_error {
            Err(TcError::Signal)
        } else {
            Ok(self.param_utils().create_def_params(def_params.into_iter()))
        }
    }

    /// Infer the given definition arguments.
    pub fn infer_def_args(&self, def_args: DefArgsId) -> TcResult<DefParamsId> {
        self.stores().def_args().map(def_args, |def_args| {
            self.infer_some_def_args(def_args, |def_arg| {
                Ok(DefParamGroupData {
                    implicit: def_arg.implicit,
                    params: self.infer_args(def_arg.args)?,
                })
            })
        })
    }

    /// Infer the given definition pattern arguments.
    pub fn infer_def_pat_args(&self, def_pat_args: DefPatArgsId) -> TcResult<DefParamsId> {
        self.stores().def_pat_args().map(def_pat_args, |def_pat_args| {
            self.infer_some_def_args(def_pat_args, |def_pat_arg| {
                Ok(DefParamGroupData {
                    implicit: def_pat_arg.implicit,
                    params: self.infer_pat_args(def_pat_arg.pat_args)?,
                })
            })
        })
    }

    /// Infer the given generic arguments (specialised
    /// for args and pat args below).
    pub fn infer_some_args<Arg>(
        &self,
        args: &[Arg],
        infer_arg_ty: impl Fn(&Arg) -> TcResult<Option<TyId>>,
        get_arg_name: impl Fn(&Arg) -> Symbol,
    ) -> TcResult<ParamsId> {
        let mut params = vec![];
        let mut has_error = false;

        for arg in args {
            // Infer the type of the argument
            let ty = match self.try_or_add_error(infer_arg_ty(arg)) {
                // Type was inferred
                Some(Some(ty)) => ty,
                // Type could not be inferred
                Some(None) => self.new_ty_hole(),
                // Error occurred
                None => {
                    has_error = true;
                    self.new_ty_hole()
                }
            };

            // Add the parameter
            params.push(ParamData { name: get_arg_name(arg), ty })
        }

        if has_error {
            Err(TcError::Signal)
        } else {
            Ok(self.param_utils().create_params(params.into_iter()))
        }
    }

    /// Infer the given arguments, producing inferred parameters.
    pub fn infer_args(&self, args: ArgsId) -> TcResult<ParamsId> {
        self.stores().args().map(args, |args| {
            self.infer_some_args(
                args,
                |arg| self.infer_term(arg.value),
                |arg| self.new_symbol_from_param_index(arg.target),
            )
        })
    }

    /// Infer the given pattern arguments, producing inferred parameters.
    pub fn infer_pat_args(&self, pat_args: PatArgsId) -> TcResult<ParamsId> {
        self.stores().pat_args().map(pat_args, |pat_args| {
            self.infer_some_args(
                pat_args,
                |pat_arg| self.infer_pat(pat_arg.pat),
                |pat_arg| self.new_symbol_from_param_index(pat_arg.target),
            )
        })
    }

    /// Infer the type of a sequence of terms which should all match.
    pub fn infer_unified_list<U: Copy>(
        &self,
        items: &[U],
        infer_item: impl Fn(U) -> TcResult<Option<TyId>>,
    ) -> TcResult<TyId> {
        let mut current_ty = self.new_ty_hole();
        let mut found_error = false;

        for term in items {
            match self.try_or_add_error(infer_item(*term)) {
                Some(Some(ty)) => {
                    match self.unification_ops().unify_tys(ty, current_ty) {
                        Ok(Unification { sub }) => {
                            // Unification succeeded
                            self.substitution_ops().apply_sub_to_ty_in_place(current_ty, &sub);
                        }
                        Err(err) => {
                            // Error in unification, try to unify the other way
                            match self.unification_ops().unify_tys(current_ty, ty) {
                                Ok(Unification { sub }) => {
                                    // Unification succeeded the other way, so use this
                                    // type as a target
                                    current_ty = ty;
                                    self.substitution_ops()
                                        .apply_sub_to_ty_in_place(current_ty, &sub);
                                }
                                Err(_) => {
                                    // Error in unification, we only consider the first error
                                    self.diagnostics().add_error(self.convert_tc_error(err));
                                    found_error = true;
                                }
                            }
                        }
                    }
                }
                Some(None) => {
                    // Hole
                }
                None => {
                    // Error in inference
                    found_error = true;
                }
            }
        }

        if found_error {
            Err(TcError::Signal)
        } else {
            Ok(current_ty)
        }
    }

    /// Infer the given parameters.
    pub fn infer_params(&self, params: ParamsId) -> TcResult<()> {
        let mut has_error = false;
        self.stores().params().map_fast(params, |params| {
            for param in params {
                match self.try_or_add_error(self.infer_ty(param.ty)) {
                    Some(_) => {}
                    None => {
                        has_error = true;
                    }
                }
            }
        });
        if has_error {
            Err(TcError::Signal)
        } else {
            Ok(())
        }
    }

    /// Infer the type of a term, or create a new a type hole if the type is
    /// unknown.
    pub fn infer_term_or_hole(&self, term: TermId) -> TcResult<TyId> {
        Ok(self.infer_term(term)?.unwrap_or_else(|| self.new_ty_hole()))
    }

    /// Infer the type of a runtime term.
    pub fn infer_runtime_term(&self, term: &RuntimeTerm) -> TyId {
        term.term_ty
    }

    /// Infer the type of a tuple term.
    pub fn infer_tuple_term(&self, term: &TupleTerm) -> TcResult<TupleTy> {
        Ok(TupleTy { data: self.infer_args(term.data)? })
    }

    /// Infer the type of a literal.
    pub fn infer_lit(&self, lit: &Lit) -> TyId {
        self.new_data_ty(match lit {
            Lit::Int(int_lit) => match int_lit.underlying.kind {
                IntLitKind::Suffixed(suffix) => match suffix {
                    IntTy::Int(s_int_ty) => match s_int_ty {
                        SIntTy::I8 => self.primitives().i8(),
                        SIntTy::I16 => self.primitives().i16(),
                        SIntTy::I32 => self.primitives().i32(),
                        SIntTy::I64 => self.primitives().i64(),
                        SIntTy::I128 => self.primitives().i128(),
                        SIntTy::ISize => self.primitives().isize(),
                        SIntTy::IBig => self.primitives().ibig(),
                    },
                    IntTy::UInt(u_int_ty) => match u_int_ty {
                        UIntTy::U8 => self.primitives().u8(),
                        UIntTy::U16 => self.primitives().u16(),
                        UIntTy::U32 => self.primitives().u32(),
                        UIntTy::U64 => self.primitives().u64(),
                        UIntTy::U128 => self.primitives().u128(),
                        UIntTy::USize => self.primitives().usize(),
                        UIntTy::UBig => self.primitives().ubig(),
                    },
                },
                // By default, we assume that all integers are i32 unless annotated otherwise.
                IntLitKind::Unsuffixed => self.primitives().i32(),
            },
            Lit::Str(_) => self.primitives().str(),
            Lit::Char(_) => self.primitives().char(),
            Lit::Float(float) => match float.underlying.kind {
                FloatLitKind::Suffixed(float_suffix) => match float_suffix {
                    FloatTy::F32 => self.primitives().f32(),
                    FloatTy::F64 => self.primitives().f64(),
                },
                // By default, we assume that all floats are f32 unless annotated otherwise.
                FloatLitKind::Unsuffixed => self.primitives().f32(),
            },
        })
    }

    /// Infer the type of a primitive term.
    pub fn infer_prim_term(&self, term: &PrimTerm) -> TcResult<TyId> {
        match term {
            PrimTerm::Lit(lit_term) => Ok(self.infer_lit(lit_term)),
            PrimTerm::List(list_term) => {
                let list_inner_type =
                    self.stores().term_list().map_fast(list_term.elements, |elements| {
                        self.try_or_add_error(
                            self.infer_unified_list(elements, |term| self.infer_term(term)),
                        )
                        .unwrap_or_else(|| self.new_ty_hole())
                    });
                let list_ty = self.new_ty(DataTy {
                    data_def: self.primitives().list(),
                    args: self.param_utils().create_positional_args_for_data_def(
                        self.primitives().list(),
                        [[self.new_term(Term::Ty(list_inner_type))]],
                    ),
                });
                Ok(list_ty)
            }
        }
    }

    /// Infer the type of a constructor term.
    pub fn infer_ctor_term(&self, term: &CtorTerm) -> DataTy {
        let data_def =
            self.stores().ctor_defs().map_fast(term.ctor.0, |terms| terms[term.ctor.1].data_def_id);
        DataTy { data_def, args: term.data_args }
    }

    /// Infer the type of a function call.
    pub fn infer_fn_call_term(
        &self,
        fn_call_term: &FnCallTerm,
        original_term_id: TermId,
    ) -> TcResult<Option<TyId>> {
        match self.infer_term(fn_call_term.subject)? {
            Some(subject_ty) => self.map_ty(subject_ty, |subject| match subject {
                Ty::Eval(term) => match self.use_term_as_ty(*term) {
                    Some(ty) => {
                        // Try the same thing, but with the evaluated type.
                        let new_subject = self.new_term(Term::Ty(ty));
                        self.infer_fn_call_term(
                            &FnCallTerm { subject: new_subject, ..*fn_call_term },
                            original_term_id,
                        )
                    }
                    None => Ok(None),
                },
                Ty::Ref(_) => {
                    // Try the same thing, but with the dereferenced type.
                    let new_subject =
                        self.new_term(Term::Deref(DerefTerm { subject: fn_call_term.subject }));
                    self.infer_fn_call_term(
                        &FnCallTerm { subject: new_subject, ..*fn_call_term },
                        original_term_id,
                    )
                    .map_err(|err| {
                        if matches!(err, TcError::NotAFunction { .. }) {
                            // Show it with the reference type:
                            TcError::NotAFunction {
                                fn_call: original_term_id,
                                actual_subject_ty: subject_ty,
                            }
                        } else {
                            err
                        }
                    })
                }
                Ty::Fn(fn_ty) => {
                    // First infer the parameters of the function call.
                    let inferred_fn_call_params = self.infer_args(fn_call_term.args)?;

                    // Unify the parameters of the function call with the parameters of the
                    // function type.
                    let unification = self
                        .unification_ops()
                        .unify_params(inferred_fn_call_params, fn_ty.params)?;

                    // Apply the substitution to the arguments.
                    self.substitution_ops()
                        .apply_sub_to_args_in_place(fn_call_term.args, &unification.sub);

                    // Create a substitution from the parameters of the function type to the
                    // parameters of the function call.
                    let arg_sub = self
                        .substitution_ops()
                        .create_sub_from_applying_args_to_params(fn_call_term.args, fn_ty.params)?;

                    // Apply the substitution to the return type of the function type.
                    let subbed_return_ty =
                        self.substitution_ops().apply_sub_to_ty(fn_ty.return_ty, &arg_sub);

                    Ok(Some(subbed_return_ty))
                }
                Ty::Universe(_) | Ty::Data(_) | Ty::Tuple(_) | Ty::Var(_) => {
                    // Type variable is not a function type.
                    Err(TcError::NotAFunction {
                        fn_call: original_term_id,
                        actual_subject_ty: subject_ty,
                    })
                }
                Ty::Hole(_) => Ok(None),
            }),
            None => {
                // We don't know the type of the subject, so we can't infer the type of the
                // call.
                Ok(None)
            }
        }
    }

    /// Infer the type of a function definition.
    ///
    /// This will infer and modify the type of the function definition, and then
    /// return it.
    pub fn infer_fn_def(&self, fn_def_id: FnDefId) -> TcResult<FnTy> {
        let fn_def = self.stores().fn_def().get(fn_def_id);
        self.infer_params(fn_def.ty.params)?;

        match fn_def.body {
            FnBody::Defined(fn_body) => {
                self.context_utils().enter_scope(fn_def_id.into(), || {
                    // @@Todo: `return` statement type inference
                    let inferred_return_ty = self.infer_term(fn_body)?;

                    // Unify the inferred return type with the declared return type.
                    let Unification { sub: return_sub } = self.unification_ops().unify_tys(
                        inferred_return_ty.unwrap_or_else(|| self.new_ty_hole()),
                        fn_def.ty.return_ty,
                    )?;

                    // Apply the substitution to the function.
                    self.traversing_utils()
                        .visit_fn_def::<!, _>(fn_def_id, &mut |atom| {
                            Ok(self
                                .substitution_ops()
                                .apply_sub_to_atom_in_place_once(atom, &return_sub))
                        })
                        .into_ok();

                    Ok(())
                })?
            }
            FnBody::Intrinsic(_) | FnBody::Axiom => {
                // Do nothing.
            }
        }

        Ok(fn_def.ty)
    }

    /// Infer the type of a variable, and return it.
    pub fn infer_var(&self, term: Symbol) -> TcResult<Option<TyId>> {
        match self.context().get_binding(term).unwrap().kind {
            BindingKind::ModMember(_, _) | BindingKind::Ctor(_, _) => {
                unreachable!("mod members and ctors should have all been resolved by now")
            }
            BindingKind::BoundVar(bound_var) => match bound_var {
                BoundVarOrigin::Fn(fn_def_id, param_index) => Ok(Some(
                    self.stores()
                        .fn_def()
                        .map_fast(fn_def_id, |fn_def| {
                            self.get_param_by_index(fn_def.ty.params, param_index)
                        })
                        .ty,
                )),
                BoundVarOrigin::FnTy(fn_ty, param_index) => Ok(Some(
                    self.stores()
                        .ty()
                        .map_fast(fn_ty, |ty| {
                            let fn_ty = ty_as_variant!(self, value ty, Fn);
                            self.get_param_by_index(fn_ty.params, param_index)
                        })
                        .ty,
                )),
                BoundVarOrigin::Data(data_def_id, def_param_index) => Ok(Some(
                    self.stores()
                        .data_def()
                        .map_fast(data_def_id, |data_def| {
                            self.get_def_param_by_index(data_def.params, def_param_index)
                        })
                        .ty,
                )),
                BoundVarOrigin::StackMember(stack_member_id) => Ok(Some(
                    self.stores()
                        .stack()
                        .map_fast(stack_member_id.0, |stack| stack.members[stack_member_id.1].ty),
                )),
                BoundVarOrigin::Hole(_, hole_kind) => match hole_kind {
                    HoleBinderKind::Hole(ty_id) => Ok(Some(ty_id)),
                    HoleBinderKind::Guess(term_id, _) => self.infer_term(term_id), /* @@Todo: unify with guess type? */
                },
            },
        }
    }

    /// Infer the type of a `return` term, and return it.
    pub fn infer_return_term(&self, return_term: &ReturnTerm) -> TcResult<TyId> {
        let _ = self.infer_term(return_term.expression)?;
        Ok(self.new_never_ty())
    }

    /// Infer the type of a deref term, and return it.
    pub fn infer_deref_term(&self, deref_term: &DerefTerm) -> TcResult<Option<TyId>> {
        match self.infer_term(deref_term.subject) {
            Ok(Some(subject_ty_id)) => {
                self.stores().ty().map_fast(subject_ty_id, |subject_ty| match subject_ty {
                    Ty::Ref(ref_ty) => Ok(Some(ref_ty.ty)),
                    Ty::Hole(_) => Ok(Some(self.new_ty_hole())),
                    _ => Err(TcError::CannotDeref {
                        subject: deref_term.subject,
                        actual_subject_ty: subject_ty_id,
                    }),
                })
            }
            s => s,
        }
    }

    /// Infer the type of a type, and return it.
    pub fn infer_ty(&self, ty_id: TyId) -> TcResult<Option<TyId>> {
        // @@Todo: cumulative type universe infers
        self.stores().ty().map(ty_id, |ty| match ty {
            Ty::Eval(eval) => self.infer_term(*eval),
            Ty::Var(var) => self.infer_var(*var),
            Ty::Tuple(tuple_ty) => {
                // Infer the parameters
                self.infer_params(tuple_ty.data)?;

                Ok(Some(self.new_small_universe_ty()))
            }
            Ty::Fn(fn_ty) => {
                // @@Todo: purity/unsafe infers

                // Infer the parameters
                self.infer_params(fn_ty.params)?;
                self.context_utils().enter_scope(ScopeKind::FnTy(ty_id), || {
                    // Given the parameters, infer the return type
                    Ok(self.infer_ty(fn_ty.return_ty)?.map(|_| self.new_small_universe_ty()))
                })
            }
            Ty::Ref(ref_ty) => {
                // Infer the inner type
                self.infer_ty(ref_ty.ty)?;
                Ok(Some(self.new_small_universe_ty()))
            }
            Ty::Data(data_ty) => {
                // Infer the arguments.
                let inferred_def_params = self.infer_def_args(data_ty.args)?;

                // Unified the inferred parameters with the declared parameters.
                let data_ty_params =
                    self.stores().data_def().map_fast(data_ty.data_def, |data_def| data_def.params);
                let Unification { sub } =
                    self.unification_ops().unify_def_params(inferred_def_params, data_ty_params)?;

                // Apply the substitution to the arguments.
                self.substitution_ops().apply_sub_to_def_args_in_place(data_ty.args, &sub);

                Ok(Some(self.new_small_universe_ty()))
            }
            Ty::Universe(universe_ty) => Ok(Some(self.new_universe_ty(universe_ty.size + 1))),
            Ty::Hole(_) => Ok(None),
        })
    }

    /// Infer the type of a loop control term, and return it.
    pub fn infer_loop_control_term(&self, _: &LoopControlTerm) -> TyId {
        // Always `never`.
        self.new_never_ty()
    }

    /// Infer the type of an unsafe term, and return it.
    pub fn infer_unsafe_term(&self, unsafe_term: &UnsafeTerm) -> TcResult<Option<TyId>> {
        // @@Todo: unsafe context
        // For now just forward to the inner term.
        self.infer_term(unsafe_term.inner)
    }

    /// Infer the type of a loop term, and return it.
    pub fn infer_loop_term(&self, loop_term: &LoopTerm) -> TcResult<Option<TyId>> {
        // Forward to the inner term.
        Ok(self.infer_block_term(&loop_term.block)?.map(|_| {
            // Always `void` until we can have expressions on breaks.
            self.new_void_ty()
        }))
    }

    /// Infer the type of a block term, and return it.
    pub fn infer_block_term(&self, block_term: &BlockTerm) -> TcResult<Option<TyId>> {
        self.stores().term_list().map_fast(block_term.statements, |statements| {
            let mut has_error = false;
            for &statement in statements {
                match self.try_or_add_error(self.infer_term(statement)) {
                    Some(Some(_)) => {}
                    None => {
                        has_error = true;
                    }
                    Some(None) => {
                        // don't consider the statement
                    }
                }
            }

            // Infer the return value
            let final_ty = self.infer_term(block_term.return_value)?;

            if has_error {
                Err(TcError::Signal)
            } else {
                Ok(final_ty)
            }
        })
    }

    /// Infer a `typeof` term, and return it.
    pub fn infer_type_of_term(&self, type_of_term: TypeOfTerm) -> TcResult<Option<TyId>> {
        let ty_of_term = self.infer_term(type_of_term.term)?;
        match ty_of_term {
            Some(ty_of_term) => {
                let ty_of_ty = self.infer_ty(ty_of_term)?;
                Ok(ty_of_ty)
            }
            None => Ok(None),
        }
    }

    /// Infer a reference term, and return its type.
    pub fn infer_ref_term(&self, ref_term: &RefTerm) -> TcResult<Option<TyId>> {
        let inner_ty = self.infer_term(ref_term.subject)?;
        match inner_ty {
            Some(inner_ty) => Ok(Some(self.new_ty(Ty::Ref(RefTy {
                ty: inner_ty,
                mutable: ref_term.mutable,
                kind: ref_term.kind,
            })))),
            None => Ok(None),
        }
    }

    /// Infer a cast term, and return its type.
    pub fn infer_cast_term(&self, cast_term: CastTerm) -> TcResult<Option<TyId>> {
        let inferred_term_ty = self.infer_term(cast_term.subject_term)?;
        match inferred_term_ty {
            Some(inferred_term_ty) => {
                let Unification { sub } =
                    self.unification_ops().unify_tys(inferred_term_ty, cast_term.target_ty)?;
                let subbed_target =
                    self.substitution_ops().apply_sub_to_ty(cast_term.target_ty, &sub);
                Ok(Some(subbed_target))
            }
            None => Ok(None),
        }
    }

    /// Infer a concrete type for a given term.
    ///
    /// If this is not possible, return `None`.
    /// To create a hole when this is not possible, use
    /// [`InferOps::infer_ty_of_term_or_hole`].
    pub fn infer_term(&self, term_id: TermId) -> TcResult<Option<TyId>> {
        self.stores().term().map(term_id, |term| match term {
            Term::Runtime(rt_term) => Ok(Some(self.infer_runtime_term(rt_term))),
            Term::Tuple(tuple_term) => Ok(Some(self.new_ty(self.infer_tuple_term(tuple_term)?))),
            Term::Prim(prim_term) => Ok(Some(self.infer_prim_term(prim_term)?)),
            Term::Ctor(ctor_term) => Ok(Some(self.new_ty(self.infer_ctor_term(ctor_term)))),
            Term::FnCall(fn_call_term) => self.infer_fn_call_term(fn_call_term, term_id),
            Term::FnRef(fn_def_id) => Ok(Some(self.new_ty(self.infer_fn_def(*fn_def_id)?))),
            Term::Var(var_term) => self.infer_var(*var_term),
            Term::Return(return_term) => Ok(Some(self.infer_return_term(return_term)?)),
            Term::Ty(ty_id) => self.infer_ty(*ty_id),
            Term::Deref(deref_term) => self.infer_deref_term(deref_term),
            Term::LoopControl(loop_control_term) => {
                Ok(Some(self.infer_loop_control_term(loop_control_term)))
            }
            Term::Unsafe(unsafe_term) => self.infer_unsafe_term(unsafe_term),
            Term::Loop(loop_term) => self.infer_loop_term(loop_term),
            Term::Block(block_term) => self.infer_block_term(block_term),
            Term::TypeOf(ty_of_term) => self.infer_type_of_term(*ty_of_term),
            Term::Ref(ref_term) => self.infer_ref_term(ref_term),
            Term::Cast(cast_term) => self.infer_cast_term(*cast_term),

            Term::DeclStackMember(_) => todo!(),
            Term::Match(_) => todo!(),
            Term::Assign(_) => todo!(),
            Term::Access(_) => todo!(),
            Term::HoleBinder(_) => todo!(),
            Term::Hole(_) => Ok(None),
        })
    }

    /// Infer the type of a pattern, and return it.
    pub fn infer_pat(&self, pat_id: PatId) -> TcResult<Option<TyId>> {
        let pat = self.get_pat(pat_id);
        match pat {
            Pat::Binding(binding) => self.infer_var(binding.name),
            Pat::Range(range_pat) => {
                let start = self.infer_lit(&range_pat.start.into());
                let end = self.infer_lit(&range_pat.end.into());
                let Unification { sub } = self.unification_ops().unify_tys(start, end)?;
                assert!(sub.is_empty());
                Ok(Some(start))
            }
            Pat::Lit(lit) => Ok(Some(self.infer_lit(&lit.into()))),
            Pat::Tuple(tuple_pat) => {
                let args = self.infer_pat_args(tuple_pat.data)?;
                Ok(Some(self.new_ty(TupleTy { data: args })))
            }
            Pat::List(list_term) => {
                let list_inner_type =
                    self.stores().pat_list().map_fast(list_term.pats, |elements| {
                        self.try_or_add_error(
                            self.infer_unified_list(elements, |pat| self.infer_pat(pat)),
                        )
                        .unwrap_or_else(|| self.new_ty_hole())
                    });
                let list_ty = self.new_ty(DataTy {
                    data_def: self.primitives().list(),
                    args: self.param_utils().create_positional_args_for_data_def(
                        self.primitives().list(),
                        [[self.new_term(Term::Ty(list_inner_type))]],
                    ),
                });
                Ok(Some(list_ty))
            }
            Pat::Ctor(ctor_pat) => {
                // @@Todo: dependent
                let _ = self.infer_def_args(ctor_pat.data_args)?;
                let _ = self.infer_def_pat_args(ctor_pat.ctor_pat_args)?;
                let data_def = self
                    .stores()
                    .ctor_defs()
                    .map_fast(ctor_pat.ctor.0, |defs| defs[ctor_pat.ctor.1].data_def_id);

                // @@todo: sub args
                Ok(Some(self.new_ty(DataTy { data_def, args: ctor_pat.data_args })))
            }
            Pat::Or(or_pat) => {
                self.stores().pat_list().map_fast(or_pat.alternatives, |alternatives| {
                    Ok(Some(self.infer_unified_list(alternatives, |pat| self.infer_pat(pat))?))
                })
            }
            Pat::If(if_pat) => {
                let cond_ty = self.infer_term(if_pat.condition)?;
                let pat_ty = self.infer_pat(if_pat.pat)?;

                match (cond_ty, pat_ty) {
                    (Some(cond_ty), Some(pat_ty)) => {
                        let Unification { sub } = self
                            .unification_ops()
                            .unify_tys(cond_ty, self.new_data_ty(self.primitives().bool()))?;
                        assert!(sub.is_empty());
                        Ok(Some(pat_ty))
                    }
                    _ => Ok(None),
                }
            }
        }
    }

    /// Infer the given data definition.
    pub fn infer_data_def(&self, _data_def_id: DataDefId) -> TcResult<()> {
        // @@Todo
        Ok(())
    }

    /// Infer the given module member.
    pub fn infer_mod_member(&self, mod_member: &ModMember) -> TcResult<()> {
        match mod_member.value {
            ModMemberValue::Data(data_def_id) => {
                self.infer_data_def(data_def_id)?;
                Ok(())
            }
            ModMemberValue::Mod(mod_def_id) => {
                self.infer_mod_def(mod_def_id)?;
                Ok(())
            }
            ModMemberValue::Fn(fn_def_id) => {
                self.infer_fn_def(fn_def_id)?;
                Ok(())
            }
        }
    }

    /// Infer the given module definition.
    pub fn infer_mod_def(&self, mod_def_id: ModDefId) -> TcResult<()> {
        let members = self.stores().mod_def().map_fast(mod_def_id, |def| def.members);
        self.stores().mod_members().map_fast(members, |members| {
            let mut has_error = false;

            // Infer each member
            for member in members {
                match self.try_or_add_error(self.infer_mod_member(member)) {
                    Some(()) => {}
                    None => has_error = true,
                }
            }

            if has_error {
                Err(TcError::Signal)
            } else {
                Ok(())
            }
        })
    }
}
