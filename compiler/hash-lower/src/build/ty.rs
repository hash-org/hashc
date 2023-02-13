//! Logic for converting `hash-tir` types into `hash-ir` types. This is done
//! in order to simplify the lowering process when it needs to deal with types
//! of items. The full [Term] structure which is defined in the `hash-tir` is
//! not required for the IR generation stage, and often has un-needed terms for
//! the lowering process. This is why this builder is used to `lower` the [Term]
//! types into the [IrTy] which is then used for the lowering process.

use hash_intrinsics::utils::PrimitiveUtils;
use hash_ir::{
    ir::Const,
    ty::{IrTy, IrTyId, VariantIdx},
};
use hash_source::constant::CONSTANT_MAP;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    data::DataTy,
    environment::env::{AccessToEnv, Env},
    lits::{Lit, PrimTerm},
    terms::{Term, TermId},
    tys::TyId,
};
use hash_utils::store::Store;

use super::Builder;
use crate::ty::new::TyLoweringCtx;

/// Convert a [LitTerm] into a [Const] value.
pub(super) fn constify_lit_term(term: TermId, tcx: &Env) -> Const {
    // tcx.term_store.map_fast(term, |term| match term {
    //     Term::Level0(Level0Term::Lit(LitTerm::Int { value })) =>
    // Const::Int(*value),
    //     Term::Level0(Level0Term::Lit(LitTerm::Char(char))) => Const::Char(*char),
    //     Term::Level0(Level0Term::Lit(LitTerm::Str(str))) => Const::Str(*str),
    //     _ => unreachable!(),
    // })
    todo!()
}

impl<'tcx> Builder<'tcx> {
    /// Get the [IrTyId] from a given [TermId]. This function will internally
    /// cache results of lowering a [TermId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(crate) fn ty_id_from_tir_term(&mut self, term: TermId) -> IrTyId {
        let ty = self.get_inferred_ty(term);

        let ctx = TyLoweringCtx { tcx: self.env(), lcx: self.ctx };
        ctx.ty_id_from_tir_ty(ty)
    }

    /// Get the [IrTy] from a given [TermId].
    pub(super) fn ty_from_tir_term(&mut self, term: TermId) -> IrTy {
        self.ty_from_tir_ty(self.get_inferred_ty(term))
    }

    /// Get the [IrTyId] from a given [TyId]. This function will internally
    /// cache results of lowering a [TyId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(super) fn ty_id_from_tir_ty(&self, ty: TyId) -> IrTyId {
        let ctx = TyLoweringCtx { tcx: self.env(), lcx: self.ctx };
        ctx.ty_id_from_tir_ty(ty)
    }

    /// Get the [IrTy] from a given [TyId].
    pub(super) fn ty_from_tir_ty(&self, ty: TyId) -> IrTy {
        self.stores().ty().map_fast(ty, |ty| {
            let ctx = TyLoweringCtx { tcx: self.env(), lcx: self.ctx };
            ctx.ty_from_tir_ty(ty)
        })
    }

    /// Get the [IrTyId] from the given [DataTy].
    pub(super) fn lower_nominal_as_id(&self, data: DataTy) -> IrTyId {
        let ctx = TyLoweringCtx { tcx: self.env(), lcx: self.ctx };
        ctx.ty_id_from_tir_data(data)
    }

    /// Assuming that the provided [TermId] is a literal term, we essentially
    /// convert the term into a [Const] and return the value of the constant
    /// as a [u128]. This literal term must be an integral type.
    pub(crate) fn evaluate_const_pat_term(&self, term: TermId) -> (Const, u128) {
        self.stores().term().map_fast(term, |term| match term {
            Term::Prim(PrimTerm::Lit(Lit::Int(lit))) => {
                let value = lit.interned_value();

                CONSTANT_MAP.map_int_constant(value, |constant| {
                    (Const::Int(value), constant.value.as_u128().unwrap())
                })
            }
            Term::Prim(PrimTerm::Lit(Lit::Char(lit))) => {
                let value = lit.value();
                (Const::Char(value), u128::from(value))
            }
            Term::Ctor(ctor_term) => {
                let bool_value = ctor_term.ctor == self.get_bool_ctor(true);
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
        self.stores().term().map_fast(term, |term| {
            match term {
                Term::Ctor(ctor_term) => {
                    // @@Verify: this seems a bit hacky to rely that all ctordefs will
                    // have the same variant indices as the ADT, but it should hold since
                    // they are lowered in the same order, and booleans also will have the
                    // same variant indices as the ADT.
                    VariantIdx::from_usize(ctor_term.ctor.1)
                }
                _ => unreachable!(),
            }
        })
    }
}
