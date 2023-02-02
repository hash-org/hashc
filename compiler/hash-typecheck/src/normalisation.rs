//! Operations for normalising terms and types.
use std::ops::ControlFlow;

use derive_more::{Constructor, Deref, From};
use hash_tir::new::{
    access::AccessTerm,
    casting::CastTerm,
    control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
    environment::context::{BindingKind, ScopeKind},
    fns::{FnBody, FnCallTerm},
    refs::{DerefTerm, RefTerm},
    scopes::{AssignTerm, BlockTerm, DeclTerm},
    symbols::Symbol,
    terms::{Term, TermId, UnsafeTerm},
    tys::{Ty, TyId, TypeOfTerm},
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
    /// Normalise the given atom.
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

    /// Normalise the given atom, and try to use it as a type.
    pub fn normalise_to_ty(&self, atom: Atom) -> TcResult<Option<TyId>> {
        match self.normalise(atom)? {
            Atom::Term(term) => match self.get_term(term) {
                Term::Ty(ty) => Ok(Some(ty)),
                Term::Var(var) => Ok(Some(self.new_ty(var))),
                _ => Ok(None),
            },
            Atom::Ty(ty) => Ok(Some(ty)),
            _ => Ok(None),
        }
    }

    /// Evaluate an atom.
    fn eval(&self, atom: Atom) -> Result<Atom, Signal> {
        self.traversing_utils().fmap_atom(atom, |atom| self.eval_once(atom))
    }

    /// Evaluate a block term.
    fn eval_block(&self, block_term: BlockTerm) -> Result<Atom, Signal> {
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

    /// Evaluate a variable.
    fn eval_var(&self, var: Symbol) -> Result<Atom, Signal> {
        match self.context().get_binding(var).unwrap().kind {
            BindingKind::Param(_, _) => Ok(self.new_term(var).into()),
            BindingKind::Arg(_, arg_id) => {
                Ok(self.stores().args().map_fast(arg_id.0, |args| args[arg_id.1].value).into())
            }
            BindingKind::StackMember(stack_member) => {
                self.stores().stack().map_fast(stack_member.0, |stack| {
                    match stack.members[stack_member.1].value {
                        Some(value) => Ok(value.into()),
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

    /// Evaluate a match term.
    fn eval_match(&self, match_term: MatchTerm) -> Result<Atom, Signal> {
        todo!()
    }

    /// Evaluate a cast term.
    fn eval_cast(&self, cast_term: CastTerm) -> Result<Atom, Signal> {
        todo!()
    }

    /// Evaluate a reference term.
    fn eval_ref(&self, ref_term: RefTerm) -> Result<Atom, Signal> {
        todo!()
    }

    /// Evaluate a dereference term.
    fn eval_deref(&self, deref_term: DerefTerm) -> Result<ControlFlow<Atom>, Signal> {
        let evaluated_inner = self.eval(deref_term.subject.into())?;
        // Reduce:
        if let Atom::Term(term) = evaluated_inner {
            if let Term::Ref(ref_expr) = self.get_term(term) {
                return Ok(ControlFlow::Break(ref_expr.subject.into()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }

    /// Evaluate an access term.
    fn eval_access(&self, access_term: AccessTerm) -> Result<ControlFlow<Atom>, Signal> {
        todo!()
    }

    /// Evaluate an unsafe term.
    fn eval_unsafe(&self, unsafe_term: UnsafeTerm) -> Result<Atom, Signal> {
        // @@Todo: handle unsafe safety
        self.eval(unsafe_term.inner.into())
    }

    /// Evaluate a `typeof` term.
    fn eval_type_of(&self, type_of_term: TypeOfTerm) -> Result<Atom, Signal> {
        // Infer the type of the term:
        let (_, ty) = self.inference_ops().infer_term(type_of_term.term, None)?;
        Ok(ty.into())
    }

    /// Evaluate a loop control term.
    fn eval_loop_control(&self, loop_control_term: LoopControlTerm) -> Signal {
        match loop_control_term {
            LoopControlTerm::Break => Signal::Break,
            LoopControlTerm::Continue => Signal::Continue,
        }
    }

    /// Evaluate an assignment term.
    fn eval_assign(&self, assign_term: AssignTerm) -> Result<ControlFlow<Atom>, Signal> {
        todo!()
    }

    /// Evaluate a declaration term.
    fn eval_decl(&self, decl_term: DeclTerm) -> Result<ControlFlow<Atom>, Signal> {
        todo!()
    }

    /// Evaluate a `return` term.
    fn eval_return(&self, return_term: ReturnTerm) -> Result<!, Signal> {
        let normalised = self.eval(return_term.expression.into())?;
        Err(Signal::Return(normalised))
    }

    /// Evaluate a `loop` term.
    fn eval_loop(&self, loop_term: LoopTerm) -> Result<Atom, Signal> {
        loop {
            match self.eval_block(loop_term.block) {
                Ok(_) | Err(Signal::Continue) => continue,
                Err(Signal::Break) => break,
                Err(e) => return Err(e),
            }
        }
        Ok(self.new_void_term().into())
    }

    /// Evaluate a term and use it as a type.
    fn eval_ty_eval(&self, term: TermId) -> Result<Atom, Signal> {
        let evaluated = self.eval(term.into())?;
        match evaluated {
            Atom::Ty(_) => Ok(evaluated),
            Atom::Term(term) => match self.get_term(term) {
                Term::Ty(ty) => Ok(ty.into()),
                _ => Ok(evaluated),
            },
            Atom::FnDef(_) | Atom::Pat(_) => unreachable!(),
        }
    }

    /// Evaluate a function call.
    fn eval_fn_call(&self, mut fn_call: FnCallTerm) -> Result<Atom, Signal> {
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
                        let sub = self.substitution_ops().create_sub_from_applying_args_to_params(
                            fn_call.args,
                            fn_def.ty.params,
                        );

                        // Apply substitution to body:
                        let result =
                            self.substitution_ops().apply_sub_to_term(defined_fn_def, &sub);

                        // Evaluate result:
                        return match self.eval(result.into()) {
                            Err(Signal::Return(result)) | Ok(result) => Ok(result),
                            Err(e) => Err(e),
                        };
                    }

                    FnBody::Intrinsic(intrinsic_id) => {
                        let args_as_terms: Vec<TermId> =
                            self.stores().args().map_fast(fn_call.args, |args| {
                                args.iter().map(|arg| arg.value).collect()
                            });

                        // Run intrinsic:
                        let result: TermId =
                            self.intrinsics().by_id().map_fast(intrinsic_id, |intrinsic| {
                                let intrinsic = intrinsic.unwrap();
                                (intrinsic.implementation)(self.0, &args_as_terms)
                            });

                        return Ok(result.into());
                    }

                    FnBody::Axiom => {
                        // Nothing further to do
                    }
                }
            }
        }

        Ok(self.new_term(fn_call).into())
    }

    /// Evaluate an atom once, for use with `fmap`.
    fn eval_once(&self, atom: Atom) -> Result<ControlFlow<Atom>, Signal> {
        match atom {
            Atom::Term(term) => match self.get_term(term) {
                // Types
                Term::Ty(_) => Ok(ControlFlow::Continue(())),

                // Introduction forms:
                Term::Ref(_)
                | Term::Tuple(_)
                | Term::Hole(_)
                | Term::FnRef(_)
                | Term::Ctor(_)
                | Term::Prim(_) => Ok(ControlFlow::Continue(())),

                // Potentially reducible forms:
                Term::TypeOf(term) => Ok(ControlFlow::Break(self.eval_type_of(term)?)),
                Term::Unsafe(unsafe_expr) => Ok(ControlFlow::Break(self.eval_unsafe(unsafe_expr)?)),
                Term::Match(match_term) => Ok(ControlFlow::Break(self.eval_match(match_term)?)),
                Term::FnCall(fn_call) => Ok(ControlFlow::Break(self.eval_fn_call(fn_call)?)),
                Term::Cast(cast_term) => Ok(ControlFlow::Break(self.eval_cast(cast_term)?)),
                Term::Var(var) => Ok(ControlFlow::Break(self.eval_var(var)?)),
                Term::Deref(deref_term) => self.eval_deref(deref_term),
                Term::Access(access_term) => self.eval_access(access_term),

                // Imperative:
                Term::LoopControl(loop_control) => Err(self.eval_loop_control(loop_control)),
                Term::Assign(assign_term) => self.eval_assign(assign_term),
                Term::Decl(decl_term) => self.eval_decl(decl_term),
                Term::Return(return_expr) => self.eval_return(return_expr)?,
                Term::Block(block_term) => Ok(ControlFlow::Break(self.eval_block(block_term)?)),
                Term::Loop(loop_term) => Ok(ControlFlow::Break(self.eval_loop(loop_term)?)),
            },
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Eval(term) => Ok(ControlFlow::Break(self.eval_ty_eval(term)?)),
                Ty::Var(var) => Ok(ControlFlow::Break(self.eval_var(var)?)),
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
}
