//! Operations for normalising terms and types.
use std::ops::ControlFlow;

use derive_more::{Constructor, Deref, From};
use hash_tir::new::{
    control::LoopControlTerm,
    environment::context::{BindingKind, ScopeKind},
    fns::FnBody,
    scopes::BlockTerm,
    symbols::Symbol,
    terms::{Term, TermId},
    tys::{Ty, TyId},
    utils::{common::CommonUtils, traversing::Atom, AccessToUtils},
};
use hash_utils::store::{PartialStore, SequenceStore, SequenceStoreKey, Store};

use crate::{
    errors::{TcError, TcResult},
    AccessToTypechecking,
};

#[derive(Constructor, Deref)]
pub struct NormalisationOps<'a, T: AccessToTypechecking>(&'a T);

/// Represents a normalisation result.
#[derive(Debug, Clone, From)]
pub enum Signal {
    Break,
    Continue,
    Return(Atom),
    Err(TcError),
}

impl<T: AccessToTypechecking> NormalisationOps<'_, T> {
    pub fn normalise(&self, atom: Atom) -> TcResult<Atom> {
        match self.eval(atom) {
            Ok(t) => Ok(t),
            Err(e) => match e {
                Signal::Break | Signal::Continue | Signal::Return(_) => {
                    panic!("Got signal when normalising: {e:?}")
                }
                Signal::Err(e) => Err(e),
            },
        }
    }

    pub fn normalise_to_ty(&self, atom: Atom) -> TcResult<Option<TyId>> {
        match self.normalise(atom)? {
            Atom::Term(term) => match self.get_term(term) {
                Term::Ty(ty) => Ok(Some(ty)),
                _ => Ok(None),
            },
            Atom::Ty(ty) => Ok(Some(ty)),
            _ => Ok(None),
        }
    }

    /// Evaluate an atom.
    pub fn eval(&self, atom: Atom) -> Result<Atom, Signal> {
        self.traversing_utils().fmap_atom(atom, |atom| self.eval_once(atom))
    }

    /// Evaluate a block term.
    pub fn eval_block(&self, block_term: BlockTerm) -> Result<Atom, Signal> {
        self.context().enter_scope(ScopeKind::Stack(block_term.stack_id), || {
            for statement in block_term
                .statements
                .to_index_range()
                .map(|i| self.stores().term_list().get_at_index(block_term.statements, i))
            {
                let _ = self.eval(statement.into())?;
            }
            self.eval(block_term.return_value.into())
        })
    }

    pub fn eval_var(&self, var: Symbol) -> Result<ControlFlow<TermId>, Signal> {
        match self.context().get_binding(var).unwrap().kind {
            BindingKind::Param(_, _) => Ok(ControlFlow::Continue(())),
            BindingKind::Arg(_, arg_id) => Ok(ControlFlow::Break(
                self.stores().args().map_fast(arg_id.0, |args| args[arg_id.1].value),
            )),
            BindingKind::StackMember(stack_member) => {
                self.stores().stack().map_fast(stack_member.0, |stack| {
                    match stack.members[stack_member.1].value {
                        Some(value) => Ok(ControlFlow::Break(value)),
                        None => {
                            // @@Todo: make this a user error
                            panic!("Tried to read uninitialised stack member")
                        }
                    }
                })
            }

            // Variables are never bound to a module member, constructor or equality.
            // @@Todo: make types better
            BindingKind::ModMember(_, _) | BindingKind::Ctor(_, _) | BindingKind::Equality(_) => {
                unreachable!()
            }
        }
    }

    /// Evaluate an atom once, for use with `fmap`.
    fn eval_once(&self, atom: Atom) -> Result<ControlFlow<Atom>, Signal> {
        // @@Todo: enter scopes
        match atom {
            Atom::Term(term) => match self.get_term(term) {
                // Forward to types:
                Term::Ty(_) => Ok(ControlFlow::Continue(())),
                // Infer type:
                Term::TypeOf(term) => {
                    let (_, ty) = self.inference_ops().infer_term(term.term, None)?;
                    Ok(ControlFlow::Break(ty.into()))
                }

                // @@Todo: different reference kinds
                Term::Ref(_) => Ok(ControlFlow::Continue(())),

                // Modalities:
                Term::Unsafe(unsafe_expr) => {
                    // @@Todo: handle unsafe safety
                    Ok(ControlFlow::Break(self.eval(unsafe_expr.inner.into())?))
                }

                // Introduction forms:
                Term::Tuple(_) | Term::Hole(_) | Term::FnRef(_) | Term::Ctor(_) | Term::Prim(_) => {
                    Ok(ControlFlow::Continue(()))
                }

                Term::Match(_) => todo!(),

                Term::FnCall(mut fn_call) => {
                    let evaluated_inner = self.eval(fn_call.subject.into())?;

                    // Beta-reduce:
                    if let Atom::Term(term) = evaluated_inner {
                        fn_call.subject = term;

                        if let Term::FnRef(fn_def_id) = self.get_term(term) {
                            let fn_def = self.get_fn_def(fn_def_id);
                            // @@Todo: handle pure/impure

                            match fn_def.body {
                                FnBody::Defined(defined_fn_def) => {
                                    // Make a substitution from the arguments to the parameters:
                                    let sub = self
                                        .substitution_ops()
                                        .create_sub_from_applying_args_to_params(
                                            fn_call.args,
                                            fn_def.ty.params,
                                        );

                                    // Apply substitution to body:
                                    let result = self
                                        .substitution_ops()
                                        .apply_sub_to_term(defined_fn_def, &sub);

                                    // Evaluate result:
                                    return match self.eval(result.into()) {
                                        Err(Signal::Return(result)) | Ok(result) => {
                                            Ok(ControlFlow::Break(result))
                                        }
                                        Err(e) => Err(e),
                                    };
                                }

                                FnBody::Intrinsic(intrinsic_id) => {
                                    let args_as_terms: Vec<TermId> =
                                        self.stores().args().map_fast(fn_call.args, |args| {
                                            args.iter().map(|arg| arg.value).collect()
                                        });

                                    // Run intrinsic:
                                    let result: TermId = self.intrinsics().by_id().map_fast(
                                        intrinsic_id,
                                        |intrinsic| {
                                            let intrinsic = intrinsic.unwrap();
                                            (intrinsic.implementation)(self.0, &args_as_terms)
                                        },
                                    );

                                    return Ok(ControlFlow::Break(result.into()));
                                }

                                FnBody::Axiom => {
                                    // Nothing further to do
                                }
                            }
                        }
                    }

                    Ok(ControlFlow::Break(self.new_term(fn_call).into()))
                }

                Term::Cast(_) => todo!(),

                Term::Deref(deref_expr) => {
                    let evaluated_inner = self.eval(deref_expr.subject.into())?;
                    // Reduce:
                    if let Atom::Term(term) = evaluated_inner {
                        if let Term::Ref(ref_expr) = self.get_term(term) {
                            return Ok(ControlFlow::Break(ref_expr.subject.into()));
                        }
                    }
                    Ok(ControlFlow::Break(evaluated_inner))
                }

                Term::Var(var) => Ok(self.eval_var(var)?.map_break(|x| x.into())),

                Term::Access(_) => todo!(),

                // Imperative:
                Term::LoopControl(loop_control) => match loop_control {
                    LoopControlTerm::Break => Err(Signal::Break),
                    LoopControlTerm::Continue => Err(Signal::Continue),
                },
                Term::Assign(_) => todo!(),
                Term::Decl(_) => {
                    todo!()
                }
                Term::Return(return_expr) => {
                    let normalised = self.eval(return_expr.expression.into())?;
                    Err(Signal::Return(normalised))
                }
                Term::Block(block_term) => Ok(ControlFlow::Break(self.eval_block(block_term)?)),
                Term::Loop(loop_term) => {
                    loop {
                        match self.eval_block(loop_term.block) {
                            Ok(_) | Err(Signal::Continue) => continue,
                            Err(Signal::Break) => break,
                            Err(e) => return Err(e),
                        }
                    }

                    Ok(ControlFlow::Break(self.new_void_term().into()))
                }
            },
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Eval(term) => {
                    let evaluated = self.eval(term.into())?;
                    match evaluated {
                        Atom::Ty(_) => Ok(ControlFlow::Break(evaluated)),
                        Atom::Term(term) => match self.get_term(term) {
                            Term::Ty(ty) => Ok(ControlFlow::Break(ty.into())),
                            _ => Ok(ControlFlow::Break(evaluated)),
                        },
                        Atom::FnDef(_) | Atom::Pat(_) => unreachable!(),
                    }
                }
                Ty::Var(var) => Ok(self
                    .eval_var(var)?
                    .map_break(|eval_result| self.use_term_as_ty_or_eval(eval_result).into())),
                Ty::Data(_)
                | Ty::Universe(_)
                | Ty::Ref(_)
                | Ty::Hole(_)
                | Ty::Tuple(_)
                | Ty::Fn(_) => Ok(ControlFlow::Continue(())),
            },
            Atom::FnDef(_) => Ok(ControlFlow::Break(atom)),
            Atom::Pat(_) => Ok(ControlFlow::Continue(())),
        }
    }

    /// Reduce a term to normal form.
    pub fn potentially_normalise_term(&self, _term_id: TermId) -> TcResult<Option<TermId>> {
        todo!()
    }
}
