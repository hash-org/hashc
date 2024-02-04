use std::{
    io::{self, Write},
    iter,
};

use hash_layout::{
    compute::LayoutComputer,
    constant::{Const, ConstKind},
    ty::{AdtFlags, ReprTy, VariantIdx, COMMON_REPR_TYS},
};
use hash_source::{
    constant::{Scalar, ScalarInt},
    FloatTy, IntTy, Size,
};
use hash_storage::store::statics::StoreId;
use hash_target::data_layout::HasDataLayout;

use crate::utils::ConstUtils;

/// is used when printing the generated IR.
pub fn pretty_print_const(
    f: &mut impl Write,
    constant: &Const,
    lc: LayoutComputer<'_>,
) -> io::Result<()> {
    match (constant.kind(), constant.ty().value()) {
        (ConstKind::Pair { data, .. }, ReprTy::Ref(inner, _, _)) => match inner.value() {
            ReprTy::Str => write!(f, "{:?}", data.value()),
            _ => Ok(()),
        },

        (ConstKind::Scalar(scalar), ty) => {
            pretty_print_scalar(f, scalar, &ty, lc.data_layout().pointer_size, false)
        }
        (ConstKind::Alloc { .. }, ReprTy::Array { .. }) => {
            write!(f, "[{}]", 2)
        }
        // We put a `zero` for fndefs.
        (ConstKind::Zero, ReprTy::FnDef { .. }) => {
            write!(f, "{}", constant.ty())
        }
        (ConstKind::Zero, _) => {
            debug_assert!(constant.ty() == COMMON_REPR_TYS.unit);
            write!(f, "()")
        }
        (_, ReprTy::Adt(def)) => {
            let utils = ConstUtils::new(lc, constant);

            if let Some(destructured) = utils.destructure_const() {
                match def.borrow().flags {
                    AdtFlags::STRUCT | AdtFlags::ENUM => {
                        write!(f, "{}", def.borrow().name)?;

                        let variant =
                            destructured.variant.expect("expected variant for destructured ADT");

                        // @@Todo: don't copy this out!
                        let variant_def = def.borrow().variant(variant).clone();

                        if AdtFlags::ENUM == def.borrow().flags {
                            write!(f, "::{}", variant_def.name)?;
                        }

                        write!(f, "(")?;
                        let mut first = true;
                        for (field, constant) in
                            iter::zip(variant_def.fields.iter(), destructured.fields)
                        {
                            if !first {
                                write!(f, ", ")?;
                            }

                            write!(f, "{}: ", field.name)?;
                            pretty_print_const(f, &constant, lc)?;

                            first = false;
                        }

                        write!(f, ")")
                    }
                    AdtFlags::TUPLE => {
                        // @@Todo: don't copy this out!
                        let variant_def = def.borrow().variant(VariantIdx::new(0)).clone();

                        write!(f, "(")?;
                        let mut first = true;
                        for (field, constant) in
                            iter::zip(variant_def.fields.iter(), destructured.fields)
                        {
                            if !first {
                                write!(f, ", ")?;
                            }

                            write!(f, "{}: ", field.name)?;
                            pretty_print_const(f, &constant, lc)?;

                            first = false;
                        }

                        write!(f, ")")
                    }
                    AdtFlags::UNION => {
                        unimplemented!("union representations aren't implemented yet")
                    }
                    _ => unreachable!(),
                }
            } else {
                Ok(())
            }
        }
        (kind, _) => {
            write!(f, "{kind:?}: {}", constant.ty())
        }
    }
}

/// Pretty printing a [Scalar] value.
pub fn pretty_print_scalar(
    f: &mut impl Write,
    scalar: Scalar,
    ty: &ReprTy,
    ptr_size: Size,
    int_shorhand: bool,
) -> io::Result<()> {
    match ty {
        ReprTy::Bool if scalar == Scalar::FALSE => write!(f, "false"),
        ReprTy::Bool if scalar == Scalar::TRUE => write!(f, "true"),
        ReprTy::Float(FloatTy::F32) => {
            write!(f, "{:?}f32", f32::try_from(scalar).unwrap())
        }
        ReprTy::Float(FloatTy::F64) => {
            write!(f, "{:?}f64", f64::try_from(scalar).unwrap())
        }
        ReprTy::Char => {
            write!(f, "{:?}", char::try_from(scalar).unwrap())
        }
        ty @ (ReprTy::Int(_) | ReprTy::UInt(_)) if int_shorhand => {
            let size = scalar.size();
            let value = scalar.to_bits(size).unwrap();
            let ty = IntTy::from(*ty);

            if ty.numeric_min(ptr_size) == value {
                write!(f, "{ty}::MIN")
            } else if ty.numeric_max(ptr_size) == value {
                write!(f, "{ty}::MAX")
            } else {
                write!(f, "{}", ScalarInt::new(scalar, ty))
            }
        }
        ty @ (ReprTy::Int(_) | ReprTy::UInt(_)) => {
            write!(f, "{}", ScalarInt::new(scalar, IntTy::from(*ty)))
        }
        ReprTy::Ref(..) | ReprTy::Fn { .. } => {
            let data = scalar.assert_bits(ptr_size);
            write!(f, "0x{:x} as {ty}", data)
        }
        _ => panic!("unexpected type for scalar: {ty:?}"),
    }
}
