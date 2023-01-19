//! Definition and lookup of intrinsics.
use std::{fmt::Debug, process};

use hash_source::identifier::Identifier;
use hash_types::new::{
    environment::env::AccessToEnv,
    fns::{FnBody, FnDef, FnDefId, FnTy},
    intrinsics::IntrinsicId,
    mods::{ModMemberData, ModMemberValue},
    terms::TermId,
    utils::common::CommonUtils,
};
use hash_utils::store::{DefaultPartialStore, PartialCloneStore, PartialStore, Store};

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
    pub implementation: fn(&(dyn AccessToPrimitives), &[TermId]) -> TermId,
}

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

    /// Create the default intrinsics.
    pub fn create<T: AccessToEnv + AccessToPrimitives + Copy>(env: T) -> Self {
        let intrinsics = Self::empty();
        let add =
            |name: &'static str,
             fn_ty: FnTy,
             implementation: fn(&(dyn AccessToPrimitives), &[TermId]) -> TermId| {
                intrinsics.add_intrinsic(env, name, fn_ty, implementation)
            };

        add(
            "abort",
            FnTy::builder().params(env.new_empty_params()).return_ty(env.new_never_ty()).build(),
            |_, _| process::exit(1),
        );

        add(
            "checked_add_i32",
            FnTy::builder().params(env.new_empty_params()).return_ty(env.new_never_ty()).build(),
            |_, _| process::exit(1),
        );

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
        implementation: fn(&(dyn AccessToPrimitives), &[TermId]) -> TermId,
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
