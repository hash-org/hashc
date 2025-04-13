//! Hash Typechecker pattern exhaustiveness module. This module contains all
//! of the machinery that is responsible for validating the exhaustiveness and
//! usefulness of patterns.
//!
//! Usefulness and exhaustiveness are inherently linked concepts, and are
//! computed in at the same time. In terms of `usefulness` we compute that if a
//! specified pattern `p` is useful in regards to a row of patterns `v` which
//! precede `p`. In other words, will this pattern `p` be ever reached if the
//! patterns `v` are specified before it. Usefulness determines if certain
//! branches in a `match` statement or other constructs that utilise patterns
//! will ever be matched.
//!
//! Exhaustiveness is similar to usefulness, but addresses the question of will
//! the provided row of patterns `v` cover all variants of some subject type.
//! For example, in the `match` block:
//! ```ignore
//! x := Some(3); // ty: Option<i32>
//! match x {
//!     Some(_) => print("there is a number");
//!     None => print("there is no number");
//! };
//! ```
//!
//! So in this example, for `x` which is of type `Option<i32>`, will the
//! patterns: [`Some(_)`, `None`] cover all cases of `Option<i32>`? In this
//! situation yes, because both variants and their inner constructors because of
//! the wildcard `_`. However, a case where this property does not hold can be
//! easily constructed:
//! ```ignore
//! x := Some(3); // ty: Option<i32>
//! match x {
//!     Some(3) => print("The number is 3!");
//!     None => print("there is no number");
//! };
//! ```
//!
//! Well here, we can come up with cases which the pattern set does not cover,
//! for example `Some(4)`. Therefore, the exhaustiveness check will conclude
//! that the provided pattern vector is not exhaustive and misses some cases.
//!
//! The implementation of this algorithm is based on the research paper:
//!
//! <http://moscova.inria.fr/~maranget/papers/warn/warn.pdf>
//!
//! inspired by and based off of the Rust Compiler implementation:
//!
//! <https://github.com/rust-lang/rust/tree/master/compiler/rustc_mir_build/src/thir/pattern/usefulness.rs>
#![feature(let_chains, if_let_guard)]

// ##GeneratedOrigin(crate): This crate only produces TIR nodes which are
// printed, and never shown as a span in any diagnostics. Therefore, all origins
// are set to `NodeOrigin::Generated`.

pub mod construct;
pub mod deconstruct;
pub mod diagnostics;
pub mod fields;
pub mod list;
pub mod lower;
pub mod matrix;
pub mod range;
pub mod stack;
pub mod storage;
pub mod usefulness;
pub mod wildcard;

use derive_more::Deref;
use diagnostics::{ExhaustivenessDiagnostics, ExhaustivenessError, ExhaustivenessWarning};
use hash_ast::ast::MatchOrigin;
use hash_ir::{HasIrCtx, IrCtx};
use hash_reporting::diagnostic::Diagnostics;
use hash_source::location::Span;
use hash_target::{HasTarget, Target};
use hash_tir::{
    context::{Context, HasContext},
    tir::{PatId, TyId},
};
use hash_tir_utils::lower::{HasTyCache, TyCache, TyLower, TyLowerEnv};
use storage::ExhaustivenessCtx;
use usefulness::Reachability;

/// General exhaustiveness context that's used when performing
/// splitting and specialisation operations.
#[derive(Copy, Clone)]
pub struct PatCtx {
    /// The term of the current column that is under investigation
    pub ty: TyId,
    /// Whether the current pattern is the whole pattern as found in a match
    /// arm, or if it's a sub-pattern.
    pub(crate) is_top_level: bool,
}

impl PatCtx {
    /// Create a new [PatCtx]
    pub fn new(ty: TyId, is_top_level: bool) -> Self {
        PatCtx { ty, is_top_level }
    }
}

#[derive(Deref)]
pub struct ExhaustivenessChecker<'env, E> {
    /// The span of the subject that is being checked for exhaustiveness
    /// or usefulness.
    subject_span: Span,

    /// The exhaustiveness store keeps track of created de-constructed patterns
    /// and usefulness constructors, basically representations used by
    /// exhaustiveness to evaluate whether something is exhaustive. Since
    /// every exhaustive instance is independent from one another, we can keep
    /// the [ExhaustivenessCtx] local to each checker, or in other words, local
    /// to the thread that is processing the job.
    ecx: ExhaustivenessCtx,

    /// Any diagnostics that are generated during the exhaustiveness check are
    /// stored here.
    diagnostics: ExhaustivenessDiagnostics,

    /// The ambient environment for target etc.
    #[deref]
    env: &'env E,

    /// Current typechecking context.
    ctx: &'env Context,
}

pub trait ExhaustivenessEnv: HasIrCtx + HasTarget + HasTyCache {}

impl<E: HasIrCtx + HasTarget + HasTyCache> ExhaustivenessEnv for E {}

impl<E: ExhaustivenessEnv> HasContext for ExhaustivenessChecker<'_, E> {
    fn context(&self) -> &Context {
        self.ctx
    }
}

impl<E: ExhaustivenessEnv> HasTyCache for ExhaustivenessChecker<'_, E> {
    fn repr_ty_cache(&self) -> &TyCache {
        self.env.repr_ty_cache()
    }
}

impl<E: ExhaustivenessEnv> HasIrCtx for ExhaustivenessChecker<'_, E> {
    fn ir_ctx(&self) -> &IrCtx {
        self.env.ir_ctx()
    }
}

impl<E: ExhaustivenessEnv> HasTarget for ExhaustivenessChecker<'_, E> {
    fn target(&self) -> &Target {
        self.env.target()
    }
}

impl<E: ExhaustivenessEnv> TyLowerEnv for ExhaustivenessChecker<'_, E> {}

impl<'env, E: ExhaustivenessEnv> ExhaustivenessChecker<'env, E> {
    /// Create a new checker.
    pub fn new(subject_span: Span, env: &'env E, ctx: &'env Context) -> Self {
        Self {
            subject_span,
            ecx: ExhaustivenessCtx::new(),
            ctx,
            diagnostics: ExhaustivenessDiagnostics::new(),
            env,
        }
    }

    /// Create a new type lowerer, converting TIR types into Repr Types.
    pub fn ty_lower(&self) -> TyLower<'_, Self> {
        TyLower::new(self)
    }

    /// Convert the [ExhaustivenessChecker] into its
    /// [ExhaustivenessDiagnostics].
    pub fn into_diagnostics(self) -> ExhaustivenessDiagnostics {
        self.diagnostics
    }

    /// Checks whether a `match` block is exhaustive from the provided patterns
    /// of each branch and whether there are any `useless` patterns that
    /// are present within the
    pub fn is_match_exhaustive(&mut self, pats: &[PatId], ty: TyId) {
        let arms = self.lower_pats_to_arms(pats, ty);
        let report = self.compute_match_usefulness(ty, &arms);

        // report if any of the match arms are unreachable...
        for (arm, reachability) in report.arm_usefulness {
            match reachability {
                Reachability::Unreachable => self
                    .diagnostics
                    .add_warning(ExhaustivenessWarning::UnreachablePat { pat: arm.id }),
                Reachability::Reachable(pats) if pats.is_empty() => {}
                Reachability::Reachable(pats) => {
                    // Sort the items as in declaration order
                    let mut items = pats.clone();
                    items.sort_unstable();

                    // @@Future add more sophisticated unreachable reporting since we might
                    // want to identify if there is a originating pattern that makes the
                    // current pattern unreachable
                    for pat in pats {
                        self.diagnostics.add_warning(ExhaustivenessWarning::UnreachablePat { pat })
                    }
                }
            }
        }

        let witnesses = report.non_exhaustiveness_witnesses;
        if !witnesses.is_empty() {
            self.diagnostics.add_error(ExhaustivenessError::NonExhaustiveMatch {
                location: self.subject_span,
                uncovered_pats: witnesses,
            })
        }
    }

    /// Checks whether the given [PatId] is irrefutable in terms of the provided
    /// [TyId] which will be used as the subject type of the refutability
    /// check.
    ///
    /// The function takes a list of [PatId]s because some of the cases that
    /// are checked for irrefutability are transpiled into a match block to
    /// avoid being more complicated than they are needed. This process
    /// occurs in [ast desugaring](hash_ast_desugaring::desugaring) module.
    pub fn is_pat_irrefutable(&mut self, pats: &[PatId], ty: TyId, origin: Option<MatchOrigin>) {
        let arms = self.lower_pats_to_arms(pats, ty);
        let report = self.compute_match_usefulness(ty, &arms);

        // We ignore whether the pattern is unreachable (i.e. whether the type is
        // empty). We only care about exhaustiveness here.
        let witnesses = report.non_exhaustiveness_witnesses;

        if !witnesses.is_empty() {
            self.diagnostics.add_error(ExhaustivenessError::RefutablePat {
                origin,
                pat: pats[0],
                uncovered_pats: witnesses,
            })
        }
    }
}

/// Wraps a type `T` to provide access to the [ExhaustivenessChecker] that
/// created it. This is used to print and convert various types and data which
/// depends on a specific [ExhaustivenessChecker] to be available.
pub struct ExhaustivenessFmtCtx<'env, T, E> {
    /// The item that is wrapped.
    pub item: T,

    /// The checker to which this item belongs to.
    pub checker: &'env ExhaustivenessChecker<'env, E>,
}

impl<'env, T, E> ExhaustivenessFmtCtx<'env, T, E> {
    /// Create a new [ExhaustivenessFmtCtx] from the given item and checker.
    pub fn new(item: T, checker: &'env ExhaustivenessChecker<'env, E>) -> Self {
        Self { item, checker }
    }

    /// Create a new [ExhaustivenessFmtCtx] from the given item and checker.
    pub fn with<U>(&self, item: U) -> ExhaustivenessFmtCtx<'env, U, E> {
        ExhaustivenessFmtCtx::new(item, self.checker)
    }
}
