use std::ops::ControlFlow;

use hash_ast_utils::lit::{FloatLitKind, IntLitKind};
use hash_storage::store::statics::StoreId;
use hash_target::primitives::{BigIntTy, FloatTy, IntTy, SIntTy, UIntTy};
use hash_tir::{
    intrinsics::{
        definitions::{f32_def, f64_def, i32_def, Primitive},
        make::IsPrimitive,
        utils::{try_use_ty_as_float_ty, try_use_ty_as_int_ty},
    },
    tir::{DataDefCtors, Lit, LitId, NodeId, PrimitiveCtorInfo, Ty, TyId},
};
use hash_tir_utils::upcast::TyUpCast;

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{already_normalised, NormaliseResult},
    tc::Tc,
    traits::OperationsOnNode,
    utils::matching::MatchResult,
};

impl<E: TcEnv> Tc<'_, E> {
    /// Potentially adjust the underlying constant of a literal after its type
    /// has been inferred.
    ///
    /// This might be needed if a literal is unsuffixed in the original source,
    /// and thus represented as something other than its true type in the
    /// `CONSTS`. After `infer_lit`, its true type will be known, and
    /// we can then adjust the underlying constant to match the true type.
    fn bake_lit_repr(&self, lit: LitId, inferred_ty: TyId) -> TcResult<()> {
        match *lit.value() {
            Lit::Float(_) => {
                if let Some(float_ty) = try_use_ty_as_float_ty(inferred_ty) {
                    lit.modify(|float| match &mut float.data {
                        Lit::Float(_) => float.bake_float(float_ty),
                        _ => unreachable!(),
                    })?;
                }
                // @@Incomplete: it is possible that exotic literal
                // types are defined, what happens then?
            }
            Lit::Int(_) => {
                if let Some(int_ty) = try_use_ty_as_int_ty(inferred_ty) {
                    lit.modify(|int| match &mut int.data {
                        Lit::Int(_) => int.bake_int(self.target(), int_ty),
                        _ => unreachable!(),
                    })?;
                }
                // @@Incomplete: as above
            }
            _ => {} // Already baked.
        }
        Ok(())
    }

    /// Match a literal with another.
    pub fn match_literal_to_literal<U: PartialEq>(&self, value: U, pat: U) -> MatchResult {
        if value == pat {
            MatchResult::Successful
        } else {
            MatchResult::Failed
        }
    }
}

impl<E: TcEnv> OperationsOnNode<LitId> for Tc<'_, E> {
    type AnnotNode = TyId;

    fn check_node(&self, lit: LitId, annotation_ty: Self::AnnotNode) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        let inferred_ty = Ty::data_ty(
            match *lit.value() {
                Lit::Int(int_lit) => {
                    match int_lit.kind {
                        IntLitKind::Suffixed(ty) => match ty {
                            IntTy::Int(s_int_ty) => match s_int_ty {
                                SIntTy::I8 => Primitive::I8,
                                SIntTy::I16 => Primitive::I16,
                                SIntTy::I32 => Primitive::I32,
                                SIntTy::I64 => Primitive::I64,
                                SIntTy::I128 => Primitive::I128,
                                SIntTy::ISize => Primitive::Isize,
                            },
                            IntTy::UInt(u_int_ty) => match u_int_ty {
                                UIntTy::U8 => Primitive::U8,
                                UIntTy::U16 => Primitive::U16,
                                UIntTy::U32 => Primitive::U32,
                                UIntTy::U64 => Primitive::U64,
                                UIntTy::U128 => Primitive::U128,
                                UIntTy::USize => Primitive::Usize,
                            },
                            IntTy::Big(big_int_ty) => match big_int_ty {
                                BigIntTy::IBig => Primitive::Ibig,
                                BigIntTy::UBig => Primitive::Ubig,
                            },
                        }
                        .def(),
                        _ => {
                            (match *annotation_ty.value() {
                                Ty::DataTy(data_ty) => match data_ty.data_def.value().ctors {
                                    DataDefCtors::Primitive(primitive_ctors) => {
                                        match primitive_ctors {
                                            PrimitiveCtorInfo::Numeric(numeric) => {
                                                // If the value is not compatible with the numeric
                                                // type,
                                                // then return `None` and the unification will fail.
                                                if numeric.is_float()
                                                    || (!numeric.is_signed()
                                                        && int_lit.is_negative())
                                                {
                                                    None
                                                } else {
                                                    Some(data_ty.data_def)
                                                }
                                            }
                                            _ => None,
                                        }
                                    }
                                    DataDefCtors::Defined(_) => None,
                                },
                                _ => None,
                            })
                            .unwrap_or_else(i32_def)
                        }
                    }
                }
                Lit::Float(float_lit) => match float_lit.kind {
                    FloatLitKind::Suffixed(ty) => match ty {
                        FloatTy::F32 => f32_def(),
                        FloatTy::F64 => f64_def(),
                    },
                    _ => {
                        (match *annotation_ty.value() {
                            Ty::DataTy(data_ty) => match data_ty.data_def.value().ctors {
                                DataDefCtors::Primitive(primitive_ctors) => match primitive_ctors {
                                    PrimitiveCtorInfo::Numeric(numeric) => {
                                        // If the value is not compatible with the numeric type,
                                        // then
                                        // return `None` and the unification will fail.
                                        if !numeric.is_float() {
                                            None
                                        } else {
                                            Some(data_ty.data_def)
                                        }
                                    }
                                    _ => None,
                                },
                                DataDefCtors::Defined(_) => None,
                            },
                            _ => None,
                        })
                        .unwrap_or_else(f64_def)
                    }
                },
                Lit::Const(constant) => {
                    let upcast = TyUpCast::new(self);
                    upcast
                        .data_def_from_repr_ty(constant.ty())
                        .expect("constant type is not primitive")
                }
            },
            lit.origin(),
        );

        self.check_by_unify(inferred_ty, annotation_ty)?;
        self.bake_lit_repr(lit, inferred_ty)?;
        Ok(())
    }

    fn try_normalise_node(&self, _item: LitId) -> NormaliseResult<ControlFlow<LitId>> {
        already_normalised()
    }

    fn unify_nodes(&self, src: LitId, target: LitId) -> TcResult<()> {
        self.unification_ok_or_mismatching_atoms(
            match (*src.value(), *target.value()) {
                (Lit::Int(i1), Lit::Int(i2)) => i1 == i2,
                (Lit::Float(f1), Lit::Float(f2)) => f1 == f2,
                (Lit::Const(c1), Lit::Const(c2)) => c1 == c2, /* @@Cowbunga: use const
                                                                * comparison method */
                _ => false,
            },
            src,
            target,
        )
    }
}
