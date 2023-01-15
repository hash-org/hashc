//! Logic for converting `hash-types` types into `hash-ir` types. This is done
//! in order to simplify the lowering process when it needs to deal with types
//! of items. The full [Term] structure which is defined in the `hash-types` is
//! not required for the IR generation stage, and often has un-needed terms for
//! the lowering process. This is why this builder is used to `lower` the [Term]
//! types into the [IrTy] which is then used for the lowering process.

use hash_ir::{
    ir::Const,
    ty::{AdtData, IrTy, IrTyId, VariantIdx},
};
use hash_source::constant::CONSTANT_MAP;
use hash_types::{
    nominals::EnumVariantValue,
    storage::GlobalStorage,
    terms::{FnLit, FnTy, Level0Term, Level1Term, LitTerm, Term, TermId},
};
use hash_utils::store::Store;

use super::Builder;
use crate::ty::TyLoweringCtx;

/// Get the [FnTy] from a given [TermId].
pub(super) fn get_fn_ty_from_term(term_id: TermId, tcx: &GlobalStorage) -> FnTy {
    tcx.term_store.map_fast(term_id, |term| match term {
        Term::Level0(Level0Term::FnLit(FnLit { fn_ty, .. })) => get_fn_ty_from_term(*fn_ty, tcx),
        Term::Level1(Level1Term::Fn(fn_ty)) => *fn_ty,
        _ => unreachable!(),
    })
}

/// Assuming that the provided [TermId] is a literal term, we essentially
/// convert the term into a [Const] and return the value of the constant
/// as a [u128]. This literal term must be an integral type.
pub(crate) fn evaluate_int_lit_term(term: TermId, tcx: &GlobalStorage) -> (Const, u128) {
    tcx.term_store.map_fast(term, |term| match term {
        Term::Level0(Level0Term::Lit(LitTerm::Int { value })) => CONSTANT_MAP
            .map_int_constant(*value, |val| {
                (Const::Int(*value), u128::from_be_bytes(val.get_bytes()))
            }),
        Term::Level0(Level0Term::Lit(LitTerm::Char(char))) => {
            (Const::Char(*char), u128::from(*char))
        }
        _ => unreachable!(),
    })
}

/// Convert a [LitTerm] into a [Const] value.
pub(super) fn constify_lit_term(term: TermId, tcx: &GlobalStorage) -> Const {
    tcx.term_store.map_fast(term, |term| match term {
        Term::Level0(Level0Term::Lit(LitTerm::Int { value })) => Const::Int(*value),
        Term::Level0(Level0Term::Lit(LitTerm::Char(char))) => Const::Char(*char),
        Term::Level0(Level0Term::Lit(LitTerm::Str(str))) => Const::Str(*str),
        _ => unreachable!(),
    })
}

impl<'tcx> Builder<'tcx> {
    /// Get the [IrTyId] from a given [TermId]. This function will internally
    /// cache results of lowering a [TermId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(crate) fn lower_term_as_id(&self, term: TermId) -> IrTyId {
        let ctx = TyLoweringCtx { tcx: self.tcx, lcx: self.ctx };
        ctx.ty_id_from_term(term)
    }

    /// Get the [IrTy] from a given [TermId].
    pub(super) fn lower_term(&self, term: TermId) -> IrTy {
        let ctx = TyLoweringCtx { tcx: self.tcx, lcx: self.ctx };
        ctx.ty_from_term(term)
    }

    /// This function will attempt to lower a provided [TermId] into a specified
    /// variant of a [AdtData]. This function assumed that the specified term is
    /// a [Term::Level0] enum variant which belongs to the specified adt,
    /// otherwise the function will panic.
    pub(crate) fn lower_enum_variant_ty(&self, adt: &AdtData, term: TermId) -> VariantIdx {
        self.tcx.term_store.map_fast(term, |term| match term {
            Term::Level0(level0_term) => match level0_term {
                Level0Term::EnumVariant(EnumVariantValue { name: variant_name, .. }) => {
                    adt.variant_idx(variant_name).unwrap()
                }
                term => panic!("expected enum variant, but got: {term:?}"),
            },
            term => panic!("expected enum variant, but got: {term:?}"),
        })
    }
}
