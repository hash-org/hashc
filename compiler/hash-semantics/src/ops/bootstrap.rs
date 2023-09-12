//! Bootstrap the typechecker, by creating and injecting primitive definitions
//! into the context.

use std::iter::once;

use hash_storage::store::statics::SequenceStoreValue;
use hash_tir::{
    self,
    building::gen,
    intrinsics::definitions::{all_intrinsics_as_mod_members, all_primitives_as_mod_members},
    mods::{ModDef, ModDefId, ModKind, ModMember, ModMemberValue},
    node::Node,
};
use hash_utils::itertools::Itertools;

use crate::environment::sem_env::AccessToSemEnv;

pub trait BootstrapOps: AccessToSemEnv {
    /// Bootstrap the typechecker, by constructing primitives and intrinsics,
    /// then creating a module containing all the primitives and the
    /// `Intrinsics` member.
    ///
    /// Returns the root module.
    fn bootstrap(&self) -> ModDefId {
        *self.root_mod_or_unset().get_or_init(|| self.make_root_mod())
    }

    /// Make a module containing all the primitives and intrinsics.
    fn make_root_mod(&self) -> ModDefId {
        // ##GeneratedOrigin: Primitives do not have a source location.
        let intrinsics_sym = gen::sym("Intrinsics");
        Node::create_gen(ModDef {
            name: gen::sym("Root"),
            kind: ModKind::Transparent,
            members: Node::create_gen(Node::<ModMember>::seq(
                all_primitives_as_mod_members()
                    .iter()
                    .copied()
                    .chain(once(Node::gen(ModMember {
                        name: intrinsics_sym,
                        value: ModMemberValue::Mod(Node::create_gen(ModDef {
                            name: intrinsics_sym,
                            kind: ModKind::Transparent,
                            members: Node::create_gen(Node::<ModMember>::seq(
                                all_intrinsics_as_mod_members().iter().copied(),
                            )),
                        })),
                    })))
                    .collect_vec(),
            )),
        })
    }
}

impl<T: AccessToSemEnv> BootstrapOps for T {}
