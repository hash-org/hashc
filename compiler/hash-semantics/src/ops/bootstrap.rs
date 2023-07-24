//! Bootstrap the typechecker, by creating and injecting primitive definitions
//! into the context.

use std::iter::once;

use hash_intrinsics::{
    intrinsics::DefinedIntrinsics,
    primitives::{primitives, DefinedPrimitives},
};
use hash_storage::store::statics::{SequenceStoreValue, SingleStoreValue};
use hash_tir::{
    self,
    mods::{ModDef, ModDefId, ModKind, ModMember, ModMemberData, ModMemberValue},
    symbols::sym,
    utils::AccessToUtils,
};
use hash_utils::itertools::Itertools;
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
            let intrinsics = self
                .intrinsics_or_unset()
                .get_or_init(|| DefinedIntrinsics::create(*self.sem_env()));

            let intrinsic_mod = self.make_intrinsic_mod(intrinsics);

            self.make_root_mod(intrinsic_mod)
        })
    }

    /// Make a module containing all the intrinsics.
    fn make_intrinsic_mod(&self, intrinsics: &DefinedIntrinsics) -> ModDefId {
        ModDef::create_with(|id| ModDef {
            id,
            name: sym("Intrinsics"),
            kind: ModKind::ModBlock,
            members: ModMember::seq(
                intrinsics
                    .as_mod_members()
                    .into_iter()
                    .map(|data| move |id| ModMember { id, name: data.name, value: data.value }),
            ),
        })
    }

    /// Make a module containing all the primitives and intrinsics.
    fn make_root_mod(&self, intrinsics_mod: ModDefId) -> ModDefId {
        ModDef::create_with(|id| ModDef {
            id,
            name: sym("Primitives"),
            kind: ModKind::Transparent,
            members: ModMember::seq(
                primitives()
                    .as_mod_members()
                    .into_iter()
                    .chain(once(ModMemberData {
                        name: sym("Intrinsics"),
                        value: ModMemberValue::Mod(intrinsics_mod),
                    }))
                    .map(|data| move |id| ModMember { id, name: data.name, value: data.value })
                    .collect_vec(),
            ),
        })
    }
}

impl<T: AccessToSemEnv> BootstrapOps for T {}
