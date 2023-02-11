//! Definition and lookup of intrinsics.
use std::{fmt::Debug, process};

use hash_source::identifier::Identifier;
use hash_tir::new::{
    data::DataDefId,
    environment::env::AccessToEnv,
    fns::{FnBody, FnDef, FnDefId, FnTy},
    intrinsics::IntrinsicId,
    lits::{Lit, PrimTerm},
    mods::{ModMemberData, ModMemberValue},
    terms::{Term, TermId},
    tys::Ty,
    utils::common::CommonUtils,
};
use hash_utils::store::{
    DefaultPartialStore, PartialCloneStore, PartialStore, SequenceStoreKey, Store,
};

use crate::{primitives::AccessToPrimitives, utils::PrimitiveUtils};

/// Information about an intrinsic.
///
/// An intrinsic contains an ID which is just a symbol internally, a
/// corresponding function definition (in order to be able to call it from the
/// code), and an implementation which is a Rust function that is called when
/// the intrinsic is called.
pub struct Intrinsic {
    /// The ID of the intrinsic.
    pub id: IntrinsicId,
    /// The function definition of the intrinsic.
    pub fn_def: FnDefId,
    /// The implementation of the intrinsic.
    ///
    /// This will be used by the compile-time evaluation part of typechecking,
    /// and as a reference for the behaviour of the intrinsic.
    pub implementation: IntrinsicImpl,
}

pub type IntrinsicImpl = fn(&(dyn AccessToPrimitives), &[TermId]) -> Result<TermId, String>;

/// Contains all the defined intrinsics, by name and by ID.
pub struct DefinedIntrinsics {
    /// Intrinsic IDs by name.
    by_name: DefaultPartialStore<Identifier, IntrinsicId>,
    /// Intrinsic data by ID.
    intrinsics: DefaultPartialStore<IntrinsicId, Intrinsic>,
}

impl Debug for DefinedIntrinsics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DefinedIntrinsics").finish()
    }
}

impl DefinedIntrinsics {
    fn empty() -> Self {
        Self { by_name: DefaultPartialStore::new(), intrinsics: DefaultPartialStore::new() }
    }

    /// Add a primitive to check for primitive data type equality.
    fn add_prim_type_eq_op<T: AccessToEnv + AccessToPrimitives + Copy>(&self, env: T) {
        let ty = env.new_small_universe_ty();
        let bool_ty = env.new_data_ty(env.primitives().bool());
        let bin_op_name = "prim_type_eq".to_string();
        self.add_intrinsic(
            env,
            bin_op_name,
            FnTy::builder().params(env.new_params(&[ty, ty])).return_ty(bool_ty).build(),
            |prim, args| {
                let (lhs, rhs) = (args[0], args[1]);
                let invalid = || Err("Invalid arguments for type equality intrinsic. Only data types with no arguments can be compared".to_string());

                if let (Term::Ty(lhs_ty), Term::Ty(rhs_ty)) = (prim.get_term(lhs), prim.get_term(rhs)) {
                    if let (Ty::Data(lhs_data), Ty::Data(rhs_data)) = (prim.get_ty(lhs_ty), prim.get_ty(rhs_ty)) {
                        if lhs_data.args.len() == 0 && rhs_data.args.len() == 0 {
                            return Ok(prim.new_bool_term(lhs_data.data_def == rhs_data.data_def));
                        }
                    }
                }

                invalid()
            },
        )
    }

    /// Add intrinsic operations for the given numeric type.
    fn add_numeric_ops<T: AccessToEnv + AccessToPrimitives + Copy>(
        &self,
        env: T,
        numeric_data_def_id: DataDefId,
        is_float: bool,
    ) {
        let numeric_ty = env.new_data_ty(numeric_data_def_id);
        let bool_ty = env.new_data_ty(env.primitives().bool());
        let numeric_name = env.get_symbol(env.get_data_def(numeric_data_def_id).name).name.unwrap();

        let bin_comparison_op = |bin_op_name: &str| {
            self.add_intrinsic(
                env,
                format!("{bin_op_name}_{numeric_name}"),
                FnTy::builder()
                    .params(env.new_params(&[numeric_ty, numeric_ty]))
                    .return_ty(bool_ty)
                    .build(),
                |prim, _| {
                    // @@Todo: properly implement this
                    Ok(prim.new_bool_term(true))
                },
            );
        };

        let bin_endo_op = |bin_op_name: &str| {
            self.add_intrinsic(
                env,
                format!("{bin_op_name}_{numeric_name}"),
                FnTy::builder()
                    .params(env.new_params(&[numeric_ty, numeric_ty]))
                    .return_ty(numeric_ty)
                    .build(),
                |_, args| {
                    // @@Todo: properly implement this
                    Ok(args[0])
                },
            );
        };

        bin_endo_op("add");
        bin_endo_op("sub");
        bin_endo_op("mul");
        bin_endo_op("div");
        bin_endo_op("neg");

        if !is_float {
            bin_endo_op("shr");
            bin_endo_op("shl");
            bin_endo_op("mod");
            bin_endo_op("bit_xor");
            bin_endo_op("bit_and");
            bin_endo_op("bit_or");
        }

        bin_comparison_op("eq");
        bin_comparison_op("neq");

        bin_comparison_op("lt");
        bin_comparison_op("leq");

        bin_comparison_op("gt");
        bin_comparison_op("geq");
    }

    /// Create the default intrinsics.
    pub fn create<T: AccessToEnv + AccessToPrimitives + Copy>(env: T) -> Self {
        let intrinsics = Self::empty();
        let prim = env.primitives();

        let add = |name: &'static str, fn_ty: FnTy, implementation: IntrinsicImpl| {
            intrinsics.add_intrinsic(env, name, fn_ty, implementation)
        };

        // Aborting
        add(
            "abort",
            FnTy::builder().params(env.new_empty_params()).return_ty(env.new_never_ty()).build(),
            |_, _| process::exit(1),
        );

        // User errors
        add(
            "user_error",
            FnTy::builder()
                .params(env.new_params(&[env.new_data_ty(prim.str())]))
                .return_ty(env.new_never_ty())
                .build(),
            |env, args| match env.get_term(args[0]) {
                Term::Prim(PrimTerm::Lit(Lit::Str(str_lit))) => Err(str_lit.value().to_string()),
                _ => Err("`user_error` expects a string literal as argument".to_string())?,
            },
        );

        // Primitive type equality
        intrinsics.add_prim_type_eq_op(env);

        intrinsics.add_numeric_ops(env, prim.u8(), false);
        intrinsics.add_numeric_ops(env, prim.i8(), false);
        intrinsics.add_numeric_ops(env, prim.u16(), false);
        intrinsics.add_numeric_ops(env, prim.i16(), false);
        intrinsics.add_numeric_ops(env, prim.u32(), false);
        intrinsics.add_numeric_ops(env, prim.i32(), false);
        intrinsics.add_numeric_ops(env, prim.u64(), false);
        intrinsics.add_numeric_ops(env, prim.i64(), false);
        intrinsics.add_numeric_ops(env, prim.u128(), false);
        intrinsics.add_numeric_ops(env, prim.i128(), false);
        intrinsics.add_numeric_ops(env, prim.ubig(), false);
        intrinsics.add_numeric_ops(env, prim.ibig(), false);

        intrinsics.add_numeric_ops(env, prim.f32(), true);
        intrinsics.add_numeric_ops(env, prim.f64(), true);

        intrinsics
    }

    /// The store of intrinsics by ID.
    pub fn by_id(&self) -> &DefaultPartialStore<IntrinsicId, Intrinsic> {
        &self.intrinsics
    }

    /// Add an intrinsic to the store.
    fn add_intrinsic<T: AccessToEnv + AccessToPrimitives>(
        &self,
        env: T,
        name: impl Into<Identifier>,
        fn_ty: FnTy,
        implementation: IntrinsicImpl,
    ) {
        let name = name.into();
        let intrinsic_id = IntrinsicId(env.new_symbol(name));
        self.by_name.insert(name, intrinsic_id);

        let fn_def = env.stores().fn_def().create_with(|id| {
            FnDef::builder()
                .id(id)
                .name(intrinsic_id.0)
                .ty(fn_ty)
                .body(FnBody::Intrinsic(intrinsic_id))
                .build()
        });
        let intrinsic_impl = Intrinsic { id: intrinsic_id, fn_def, implementation };
        self.intrinsics.insert(intrinsic_id, intrinsic_impl);
    }

    /// Get an intrinsic ID by its name.
    pub fn get_id(&self, name: impl Into<Identifier>) -> IntrinsicId {
        self.by_name.get(name.into()).unwrap()
    }

    /// Create a set of module members for the defined intrinsics.
    pub fn as_mod_members(&self) -> Vec<ModMemberData> {
        self.intrinsics
            .internal_data()
            .borrow()
            .values()
            .map(|intrinsic| ModMemberData {
                name: intrinsic.id.0,
                value: ModMemberValue::Fn(intrinsic.fn_def),
            })
            .collect()
    }
}

/// Trait to be able to access intrinsics.
///
/// This should be implemented by the typechecking environment.
pub trait AccessToIntrinsics {
    fn intrinsics(&self) -> &DefinedIntrinsics;
}
