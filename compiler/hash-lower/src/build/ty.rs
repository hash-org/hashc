//! Logic for converting `hash-types` types into `hash-ir` types. This is done
//! in order to simplify the lowering process when it needs to deal with types
//! of items. The full [Term] structure which is defined in the `hash-types` is
//! not required for the IR generation stage, and often has un-needed terms for
//! the lowering process. This is why this builder is used to `lower` the [Term]
//! types into the [IrTy] which is then used for the lowering process.

use hash_ir::{
    ir::Const,
    ty::{IrTy, IrTyId, VariantIdx},
};
use hash_source::{constant::CONSTANT_MAP, identifier::IDENTS};
use hash_types::{
    nominals::{EnumVariantValue, NominalDefId},
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

    /// Get the [IrTyId] from the given [NominalDefId].
    pub(super) fn lower_nominal_as_id(&self, nominal: NominalDefId) -> IrTyId {
        let ctx = TyLoweringCtx { tcx: self.tcx, lcx: self.ctx };
        ctx.ty_id_from_nominal(nominal)
    }

    /// Assuming that the provided [TermId] is a literal term, we essentially
    /// convert the term into a [Const] and return the value of the constant
    /// as a [u128]. This literal term must be an integral type.
    pub(crate) fn evaluate_const_pat_term(&self, term: TermId) -> (Const, u128) {
        self.tcx.term_store.map_fast(term, |ty| match ty {
            Term::Level0(Level0Term::Lit(LitTerm::Int { value })) => CONSTANT_MAP
                .map_int_constant(*value, |val| {
                    (Const::Int(*value), u128::from_be_bytes(val.get_bytes()))
                }),
            Term::Level0(Level0Term::Lit(LitTerm::Char(char))) => {
                (Const::Char(*char), u128::from(*char))
            }
            Term::Level0(Level0Term::EnumVariant(_)) => {
                let variant_value = self.evaluate_enum_variant_as_index(term);
                let bool_value = variant_value.index() == 1;
                (Const::Bool(bool_value), u128::from(bool_value))
            }
            _ => unreachable!(),
        })
    }

    /// This function will attempt to lower a provided [TermId] into a
    /// [VariantIdx]. This function assumed that the specified term is
    /// a [Term::Level0] enum variant which belongs to the specified adt,
    /// otherwise the function will panic.
    pub(crate) fn evaluate_enum_variant_as_index(&self, term: TermId) -> VariantIdx {
        self.tcx.term_store.map_fast(term, |term| match term {
            Term::Level0(level0_term) => match level0_term {
                Level0Term::EnumVariant(EnumVariantValue { name, def_id }) => {
                    // we essentially re-compute the variant type, and then
                    // compute the variant name index. This should be done
                    // reasonably cheaply since the type of the nominal has
                    // already been lowered, and then it is just a matter of
                    // looking up the cached type.
                    let ty = self.lower_nominal_as_id(*def_id);

                    self.ctx.map_ty(ty, |ty| {
                        match ty {
                            IrTy::Adt(adt) => {
                                self.ctx.map_adt(*adt, |_, adt| adt.variant_idx(name).unwrap())
                            }
                            // @@Hack: The only case this could be is boolean type, since we don't
                            // represent it as an ADT, but it's own type.  So we just match on the
                            // variant name and return the correct index.
                            _ => match *name {
                                i if i == IDENTS.r#true => VariantIdx::new(1),
                                i if i == IDENTS.r#false => VariantIdx::new(0),
                                _ => unreachable!(),
                            },
                        }
                    })
                }
                term => panic!("expected enum variant, but got: {term:?}"),
            },
            term => panic!("expected enum variant, but got: {term:?}"),
        })
    }
}
