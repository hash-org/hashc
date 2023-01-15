//! Operations to check types of terms and patterns.

use derive_more::Constructor;
use hash_ast::ast::{FloatLitKind, IntLitKind};
use hash_intrinsics::{primitives::AccessToPrimitives, utils::PrimitiveUtils};
use hash_source::constant::{FloatTy, IntTy, SIntTy, UIntTy};
use hash_types::{
    new::{
        args::{ArgsId, PatArgsId},
        control::{LoopControlTerm, LoopTerm, ReturnTerm},
        data::{CtorTerm, DataTy},
        defs::{DefArgsId, DefParamGroupData, DefParamsId, DefPatArgsId},
        environment::{
            context::{BindingKind, BoundVarOrigin, ScopeKind},
            env::AccessToEnv,
        },
        fns::{FnBody, FnCallTerm, FnDefId, FnTy},
        holes::HoleBinderKind,
        lits::{Lit, PrimTerm},
        params::{ParamData, ParamsId},
        pats::PatId,
        refs::DerefTerm,
        scopes::BlockTerm,
        symbols::Symbol,
        terms::{RuntimeTerm, Term, TermId, UnsafeTerm},
        tuples::{TupleTerm, TupleTy},
        tys::{Ty, TyId},
        utils::{common::CommonUtils, AccessToUtils},
    },
    ty_as_variant,
};
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey, Store};

use super::{common::CommonOps, AccessToOps};
use crate::{
    impl_access_to_tc_env,
    new::{
        diagnostics::error::{TcError, TcResult},
        environment::tc_env::{AccessToTcEnv, TcEnv},
    },
};

#[derive(Constructor)]
pub struct CheckOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(CheckOps<'tc>);

impl<'tc> CheckOps<'tc> {
    /// Check the given generic definition arguments (specialised for args and
    /// pat args below)
    fn check_some_def_args<DefArgGroup>(
        &self,
        def_args: &[DefArgGroup],
        check_def_arg_group: impl Fn(&DefArgGroup) -> TcResult<DefParamGroupData>,
    ) -> TcResult<DefParamsId> {
        // @@Todo: dependent definition parameters
        let mut def_params = vec![];
        let mut has_error = false;

        for group in def_args {
            match self.try_or_add_error(check_def_arg_group(group)) {
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

    /// Check the given definition arguments.
    pub fn check_def_args(&self, def_args: DefArgsId) -> TcResult<DefParamsId> {
        self.stores().def_args().map(def_args, |def_args| {
            self.check_some_def_args(def_args, |def_arg| {
                let implicit =
                    self.stores().def_params().map_fast(def_arg.param_group.0, |params| {
                        params[def_arg.param_group.1].implicit
                    });
                Ok(DefParamGroupData { implicit, params: self.check_args(def_arg.args)? })
            })
        })
    }

    /// Check the given definition pattern arguments.
    pub fn check_def_pat_args(&self, def_pat_args: DefPatArgsId) -> TcResult<DefParamsId> {
        self.stores().def_pat_args().map(def_pat_args, |def_pat_args| {
            self.check_some_def_args(def_pat_args, |def_pat_arg| {
                let implicit =
                    self.stores().def_params().map_fast(def_pat_arg.param_group.0, |params| {
                        params[def_pat_arg.param_group.1].implicit
                    });
                Ok(DefParamGroupData {
                    implicit,
                    params: self.check_pat_args(def_pat_arg.pat_args)?,
                })
            })
        })
    }

    /// Check the given generic arguments (specialised
    /// for args and pat args below).
    fn check_some_args<Arg>(
        &self,
        args: &[Arg],
        check_arg_ty: impl Fn(&Arg) -> TcResult<Option<TyId>>,
        get_arg_name: impl Fn(&Arg) -> Symbol,
    ) -> TcResult<ParamsId> {
        let mut params = vec![];
        let mut has_error = false;

        for arg in args {
            // Check the type of the argument
            let ty = match self.try_or_add_error(check_arg_ty(arg)) {
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
            params.push(ParamData { name: get_arg_name(arg), ty, default_value: None })
        }

        if has_error {
            Err(TcError::Signal)
        } else {
            Ok(self.param_utils().create_params(params.into_iter()))
        }
    }

    /// Check the given arguments, producing inferred parameters.
    pub fn check_args(&self, args: ArgsId) -> TcResult<ParamsId> {
        self.stores().args().map(args, |args| {
            self.check_some_args(
                args,
                |arg| self.check_term(arg.value),
                |arg| self.new_symbol_from_param_index(arg.target),
            )
        })
    }

    /// Check the given pattern arguments, producing inferred parameters.
    pub fn check_pat_args(&self, pat_args: PatArgsId) -> TcResult<ParamsId> {
        self.stores().pat_args().map(pat_args, |pat_args| {
            self.check_some_args(
                pat_args,
                |pat_arg| self.check_pat(pat_arg.pat),
                |pat_arg| self.new_symbol_from_param_index(pat_arg.target),
            )
        })
    }

    /// Check the type of a sequence of terms which should all match.
    pub fn check_unified_term_list(&self, terms: &[TermId]) -> TcResult<TyId> {
        let mut current_ty = self.new_ty_hole();
        let mut found_error = false;

        for term in terms {
            match self.try_or_add_error(self.check_term(*term)) {
                Some(Some(ty)) => {
                    match self.unify_ops().unify_tys(ty, current_ty) {
                        Ok(sub) => {
                            // Unification succeeded
                            self.substitute_ops().apply_sub_to_ty_in_place(current_ty, &sub);
                        }
                        Err(err) => {
                            // Error in unification, try to unify the other way
                            match self.unify_ops().unify_tys(current_ty, ty) {
                                Ok(sub) => {
                                    // Unification succeeded the other way, so use this
                                    // type as a target
                                    current_ty = ty;
                                    self.substitute_ops()
                                        .apply_sub_to_ty_in_place(current_ty, &sub);
                                }
                                Err(_) => {
                                    // Error in unification, we only consider the first error
                                    self.diagnostics().add_error(err);
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

    /// Check the given parameters.
    pub fn check_params(&self, _params: ParamsId) -> TcResult<()> {
        todo!()
    }

    /// Check the type of a term, or create a new a type hole if the type is
    /// unknown.
    pub fn check_term_or_hole(&self, term: TermId) -> TcResult<TyId> {
        Ok(self.check_term(term)?.unwrap_or_else(|| self.new_ty_hole()))
    }

    /// Check the type of a runtime term.
    pub fn check_runtime_term(&self, term: &RuntimeTerm) -> TyId {
        term.term_ty
    }

    /// Check the type of a tuple term.
    pub fn check_tuple_term(&self, term: &TupleTerm) -> TcResult<TupleTy> {
        match term.original_ty {
            Some(ty) => Ok(ty),
            None => Ok(TupleTy { data: self.check_args(term.data)? }),
        }
    }

    /// Check the type of a primitive term.
    pub fn check_prim_term(&self, term: &PrimTerm) -> TcResult<TyId> {
        match term {
            PrimTerm::Lit(lit_term) => Ok(self.new_data_ty(match lit_term {
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
            })),
            PrimTerm::List(list_term) => {
                let list_inner_type =
                    self.stores().term_list().map_fast(list_term.elements, |elements| {
                        self.try_or_add_error(self.check_unified_term_list(elements))
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

    /// Check the type of a constructor term.
    pub fn check_ctor_term(&self, term: &CtorTerm) -> DataTy {
        let data_def =
            self.stores().ctor_defs().map_fast(term.ctor.0, |terms| terms[term.ctor.1].data_def_id);
        DataTy { data_def, args: term.data_args }
    }

    /// Check the type of a function call.
    pub fn check_fn_call_term(
        &self,
        term: &FnCallTerm,
        original_term_id: TermId,
    ) -> TcResult<Option<TyId>> {
        match self.check_term(term.subject)? {
            Some(subject_ty) => self.map_ty(subject_ty, |subject| match subject {
                Ty::Eval(_) => {
                    // @@Todo: Normalise
                    Ok(None)
                }
                Ty::Ref(_) => {
                    // Try the same thing, but with the dereferenced type.
                    let new_subject =
                        self.new_term(Term::Deref(DerefTerm { subject: term.subject }));
                    self.check_fn_call_term(
                        &FnCallTerm { subject: new_subject, ..*term },
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
                    let inferred_fn_call_params = self.check_args(term.args)?;

                    // Unify the parameters of the function call with the parameters of the
                    // function type.
                    let sub =
                        self.unify_ops().unify_params(inferred_fn_call_params, fn_ty.params)?;

                    // Apply the substitution to the arguments.
                    self.substitute_ops().apply_sub_to_args_in_place(term.args, &sub);

                    // Create a substitution from the parameters of the function type to the
                    // parameters of the function call.
                    let arg_sub = self
                        .substitute_ops()
                        .create_sub_from_applying_args_to_params(term.args, fn_ty.params)?;

                    // Apply the substitution to the return type of the function type.
                    let subbed_return_ty =
                        self.substitute_ops().apply_sub_to_ty(fn_ty.return_ty, &arg_sub);

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
                // We don't know the type of the subject, so we can't check the type of the
                // call.
                Ok(None)
            }
        }
    }

    /// Check the type of a function definition.
    ///
    /// This will check and modify the type of the function definition, and then
    /// return it.
    pub fn check_fn_def(&self, fn_def_id: FnDefId) -> TcResult<FnTy> {
        let fn_def = self.stores().fn_def().get(fn_def_id);
        self.check_params(fn_def.ty.params)?;

        match fn_def.body {
            FnBody::Defined(fn_body) => self.context_ops().enter_scope(fn_def_id.into(), || {
                // @@Todo: `return` statement type inference
                let inferred_return_ty = self.check_term(fn_body)?;

                // Unify the inferred return type with the declared return type.
                let return_sub = self.unify_ops().unify_tys(
                    inferred_return_ty.unwrap_or_else(|| self.new_ty_hole()),
                    fn_def.ty.return_ty,
                )?;

                // Apply the substitution to the parameters.
                self.substitute_ops().apply_sub_to_params_in_place(fn_def.ty.params, &return_sub);
                self.substitute_ops().apply_sub_to_term_in_place(fn_body, &return_sub);
                self.substitute_ops().apply_sub_to_ty_in_place(fn_def.ty.return_ty, &return_sub);

                Ok(())
            })?,
            FnBody::Intrinsic(_) | FnBody::Axiom => {
                // Do nothing.
            }
        }

        Ok(fn_def.ty)
    }

    /// Check the type of a variable, and return it.
    pub fn check_var(&self, term: Symbol) -> TcResult<Option<TyId>> {
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
                BoundVarOrigin::HoleBinder(hole_binder) => match hole_binder.kind {
                    HoleBinderKind::Hole(ty_id) => Ok(Some(ty_id)),
                    HoleBinderKind::Guess(term_id) => self.check_term(term_id),
                },
            },
        }
    }

    /// Check the type of a `return` term, and return it.
    pub fn check_return_term(&self, return_term: &ReturnTerm) -> TcResult<TyId> {
        let _ = self.check_term(return_term.expression)?;
        Ok(self.new_never_ty())
    }

    /// Check the type of a deref term, and return it.
    pub fn check_deref_term(&self, deref_term: &DerefTerm) -> TcResult<Option<TyId>> {
        match self.check_term(deref_term.subject) {
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

    /// Check the type of a type, and return it.
    pub fn check_ty(&self, ty_id: TyId) -> TcResult<Option<TyId>> {
        // @@Todo: cumulative type universe checks
        self.stores().ty().map(ty_id, |ty| match ty {
            Ty::Eval(eval) => self.check_term(*eval),
            Ty::Var(var) => self.check_var(*var),
            Ty::Tuple(tuple_ty) => {
                // Check the parameters
                self.check_params(tuple_ty.data)?;

                Ok(Some(self.new_small_universe_ty()))
            }
            Ty::Fn(fn_ty) => {
                // @@Todo: purity/unsafe checks

                // Check the parameters
                self.check_params(fn_ty.params)?;
                self.context_ops().enter_scope(ScopeKind::FnTy(ty_id), || {
                    // Given the parameters, check the return type
                    Ok(self.check_ty(fn_ty.return_ty)?.map(|_| self.new_small_universe_ty()))
                })
            }
            Ty::Ref(ref_ty) => {
                // Check the inner type
                self.check_ty(ref_ty.ty)?;
                Ok(Some(self.new_small_universe_ty()))
            }
            Ty::Data(data_ty) => {
                // Check the arguments.
                let inferred_def_params = self.check_def_args(data_ty.args)?;

                // Unified the inferred parameters with the declared parameters.
                let data_ty_params =
                    self.stores().data_def().map_fast(data_ty.data_def, |data_def| data_def.params);
                let sub = self.unify_ops().unify_def_params(inferred_def_params, data_ty_params)?;

                // Apply the substitution to the arguments.
                self.substitute_ops().apply_sub_to_def_args_in_place(data_ty.args, &sub);

                Ok(Some(self.new_small_universe_ty()))
            }
            Ty::Universe(universe_ty) => Ok(Some(self.new_universe_ty(universe_ty.size + 1))),
            Ty::Hole(_) => Ok(None),
        })
    }

    /// Check the type of a loop control term, and return it.
    fn check_loop_control_term(&self, _: &LoopControlTerm) -> TyId {
        // Always `never`.
        self.new_never_ty()
    }

    /// Check the type of an unsafe term, and return it.
    fn check_unsafe_term(&self, unsafe_term: &UnsafeTerm) -> TcResult<Option<TyId>> {
        // @@Todo: unsafe context
        // For now just forward to the inner term.
        self.check_term(unsafe_term.inner)
    }

    /// Check the type of a loop term, and return it.
    pub fn check_loop_term(&self, loop_term: &LoopTerm) -> TcResult<Option<TyId>> {
        // Forward to the inner term.
        Ok(self.check_block_term(&loop_term.block)?.map(|_| {
            // Always `void` until we can have expressions on breaks.
            self.new_void_ty()
        }))
    }

    /// Check the type of a block term, and return it.
    pub fn check_block_term(&self, block_term: &BlockTerm) -> TcResult<Option<TyId>> {
        self.stores().term_list().map_fast(block_term.statements, |statements| {
            let mut _final_ty = Ty::Tuple(TupleTy { data: ParamsId::empty() });
            for _statement in statements {
                todo!()
            }
        });
        todo!()
    }

    // @@Todo: checking for other definitions.

    /// Check a concrete type for a given term.
    ///
    /// If this is not possible, return `None`.
    /// To create a hole when this is not possible, use
    /// [`CheckOps::check_ty_of_term_or_hole`].
    pub fn check_term(&self, term_id: TermId) -> TcResult<Option<TyId>> {
        self.stores().term().map(term_id, |term| {
            match term {
                Term::Runtime(rt_term) => Ok(Some(self.check_runtime_term(rt_term))),
                Term::Tuple(tuple_term) => {
                    Ok(Some(self.new_ty(self.check_tuple_term(tuple_term)?)))
                }
                Term::Prim(prim_term) => Ok(Some(self.check_prim_term(prim_term)?)),
                Term::Ctor(ctor_term) => Ok(Some(self.new_ty(self.check_ctor_term(ctor_term)))),
                Term::FnCall(fn_call_term) => self.check_fn_call_term(fn_call_term, term_id),
                Term::FnRef(fn_def_id) => Ok(Some(self.new_ty(self.check_fn_def(*fn_def_id)?))),
                Term::Var(var_term) => self.check_var(*var_term),
                Term::Return(return_term) => Ok(Some(self.check_return_term(return_term)?)),
                Term::Ty(ty_id) => self.check_ty(*ty_id),
                Term::Deref(deref_term) => self.check_deref_term(deref_term),
                Term::LoopControl(loop_control_term) => {
                    Ok(Some(self.check_loop_control_term(loop_control_term)))
                }
                Term::Unsafe(unsafe_term) => self.check_unsafe_term(unsafe_term),
                Term::Loop(loop_term) => self.check_loop_term(loop_term),

                Term::Block(_) => todo!(),
                Term::Match(_) => todo!(),
                Term::DeclStackMember(_) => todo!(),
                Term::Assign(_) => todo!(),
                Term::Access(_) => todo!(),
                Term::Cast(_) => todo!(),
                Term::TypeOf(_) => todo!(),
                Term::HoleBinder(_) => todo!(),
                Term::Ref(_ref_term) => {
                    todo!()
                    // let inner_ty =
                    // self.check_ty_of_term_or_hole(ref_term.subject);
                    // Ok(Some(self.new_ty(Ty::Ref(RefTy {
                    //     ty: inner_ty,
                    //     mutable: ref_term.mutable,
                    //     kind: ref_term.kind,
                    // }))))
                }
                Term::Hole(_) => Ok(None),
            }
        })
    }

    pub fn check_pat(&self, _value: PatId) -> TcResult<Option<TyId>> {
        todo!()
    }
}
