use hash_storage::store::statics::StoreId;
use hash_target::primitives::{BigIntTy, FloatTy, IntTy, SIntTy, UIntTy};
use hash_tir::{
    context::Context,
    intrinsics::{
        definitions::{char_def, f32_def, f64_def, i32_def, str_def, Primitive},
        make::IsPrimitive,
    },
    tir::{DataDefCtors, Lit, LitId, NodeId, PrimitiveCtorInfo, Ty, TyId},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        OperationsOnNode,
    },
};

impl<E: TcEnv> OperationsOnNode<LitId> for Tc<'_, E> {
    type TyNode = TyId;

    fn check_node(
        &self,
        _ctx: &mut Context,
        lit: LitId,
        annotation_ty: Self::TyNode,
    ) -> TcResult<()> {
        self.normalise_and_check_ty(annotation_ty)?;
        let inferred_ty = Ty::data_ty(
            match *lit.value() {
                Lit::Int(int_lit) => {
                    match int_lit.kind() {
                        Some(ty) => match ty {
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
                        None => {
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
                Lit::Str(_) => str_def(),
                Lit::Char(_) => char_def(),
                Lit::Float(float_lit) => match float_lit.kind() {
                    Some(ty) => match ty {
                        FloatTy::F32 => f32_def(),
                        FloatTy::F64 => f64_def(),
                    },
                    None => {
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
            },
            lit.origin(),
        );

        self.check_by_unify(inferred_ty, annotation_ty)?;
        self.bake_lit_repr(lit, inferred_ty)?;
        Ok(())
    }

    fn normalise_node(
        &self,
        _ctx: &mut Context,
        _opts: &NormalisationOptions,
        _item: LitId,
    ) -> NormaliseResult<LitId> {
        todo!()
    }

    fn unify_nodes(
        &self,
        _ctx: &mut Context,
        _opts: &UnificationOptions,
        _src: LitId,
        _target: LitId,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute_node(&self, _sub: &hash_tir::sub::Sub, _target: LitId) {
        todo!()
    }
}
