//! Bootstrap the typechecker, by creating and injecting primitive definitions
//! into the context.

use std::iter::once;

use hash_storage::store::statics::SequenceStoreValue;
use hash_tir::{
    self,
    building::gen,
    mods::{ModDef, ModDefId, ModKind, ModMember, ModMemberValue},
    node::{Node, NodeOrigin},
    utils::AccessToUtils,
};
use hash_utils::itertools::Itertools;
use once_cell::unsync::OnceCell;

use crate::environment::sem_env::AccessToSemEnv;

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
    fn make_intrinsic_mod(&self) -> ModDefId {
        // ##GeneratedOrigin: Intrinsics do not have a source location.
        Node::create_at(
            ModDef {
                name: gen::sym("Intrinsics"),
                kind: ModKind::ModBlock,
                members: Node::create_at(
                    Node::<ModMember>::seq(intrinsics.as_mod_members().into_iter().map(|data| {
                        Node::at(
                            ModMember { name: data.name, value: data.value },
                            NodeOrigin::Generated,
                        )
                    })),
                    NodeOrigin::Generated,
                ),
            },
            NodeOrigin::Generated,
        )
    }

    /// Make a module containing all the primitives and intrinsics.
    fn make_root_mod(&self) -> ModDefId {
        // ##GeneratedOrigin: Primitives do not have a source location.
        Node::create_at(
            ModDef {
                name: gen::sym("Primitives"),
                kind: ModKind::Transparent,
                members: Node::create_at(
                    Node::<ModMember>::seq(
                        primitives()
                            .as_mod_members()
                            .into_iter()
                            .chain(once(Node::at(
                                ModMember {
                                    name: gen::sym("Intrinsics"),
                                    value: ModMemberValue::Mod(intrinsics_mod),
                                },
                                NodeOrigin::Generated,
                            )))
                            .collect_vec(),
                    ),
                    NodeOrigin::Generated,
                ),
            },
            NodeOrigin::Generated,
        )
    }
}

impl<T: AccessToSemEnv> BootstrapOps for T {}
