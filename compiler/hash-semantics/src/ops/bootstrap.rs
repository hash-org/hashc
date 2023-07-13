//! Bootstrap the typechecker, by creating and injecting primitive definitions
//! into the context.

use std::iter::once;

use hash_intrinsics::{intrinsics::DefinedIntrinsics, primitives::DefinedPrimitives};
use hash_tir::{
    mods::{ModDefData, ModDefId, ModKind, ModMemberData, ModMemberValue},
    symbols::sym,
    utils::AccessToUtils,
};
use once_cell::unsync::OnceCell;

use crate::environment::sem_env::AccessToSemEnv;

pub type DefinedPrimitivesOrUnset = OnceCell<DefinedPrimitives>;
pub type DefinedIntrinsicsOrUnset = OnceCell<DefinedIntrinsics>;

pub trait BootstrapOps: AccessToSemEnv + AccessToUtils {
    /// Bootstrap the typechecker, by constructing primitives and intrinsics,
    /// then creating a module containing all the primitives and the
    /// `Intrinsics` member.
    ///
    /// Returns the root module.
    fn bootstrap(&self) -> ModDefId {
        *self.root_mod_or_unset().get_or_init(|| {
            let primitives =
                self.primitives_or_unset().get_or_init(|| DefinedPrimitives::create(self.env()));

            let intrinsics = self
                .intrinsics_or_unset()
                .get_or_init(|| DefinedIntrinsics::create(*self.sem_env()));

            let intrinsic_mod = self.make_intrinsic_mod(intrinsics);

            self.make_root_mod(primitives, intrinsic_mod)
        })
    }

    /// Make a module containing all the intrinsics.
    fn make_intrinsic_mod(&self, intrinsics: &DefinedIntrinsics) -> ModDefId {
        self.mod_utils().create_mod_def(ModDefData {
            name: sym("Intrinsics"),
            kind: ModKind::ModBlock,
            members: self.mod_utils().create_mod_members(intrinsics.as_mod_members(self.env())),
        })
    }

    /// Make a module containing all the primitives and intrinsics.
    fn make_root_mod(&self, primitives: &DefinedPrimitives, intrinsics_mod: ModDefId) -> ModDefId {
        self.mod_utils().create_mod_def(ModDefData {
            name: sym("Primitives"),
            kind: ModKind::Transparent,
            members: self.mod_utils().create_mod_members(
                primitives
                    .as_mod_members(self.env())
                    .into_iter()
                    .chain(once(ModMemberData {
                        name: sym("Intrinsics"),
                        value: ModMemberValue::Mod(intrinsics_mod),
                    }))
                    .collect::<Vec<_>>(),
            ),
        })
    }
}

impl<T: AccessToSemEnv> BootstrapOps for T {}
