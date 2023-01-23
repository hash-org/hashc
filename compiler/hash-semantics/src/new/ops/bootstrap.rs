//! Bootstrap the typechecker, by creating and injecting primitive definitions
//! into the context.

use hash_intrinsics::{intrinsics::DefinedIntrinsics, primitives::DefinedPrimitives};
use hash_tir::new::{
    mods::{ModDefData, ModDefId, ModKind},
    utils::{common::CommonUtils, AccessToUtils},
};
use once_cell::unsync::OnceCell;

use crate::new::environment::tc_env::AccessToTcEnv;

pub type DefinedPrimitivesOrUnset = OnceCell<DefinedPrimitives>;
pub type DefinedIntrinsicsOrUnset = OnceCell<DefinedIntrinsics>;

pub trait BootstrapOps: AccessToTcEnv + AccessToUtils {
    /// Bootstrap the typechecker, by constructing primitives and intrinsics,
    /// then creating modules of the two and giving them to
    /// the provided closure.
    ///
    /// Returns `(primitives_mod, intrinsics_mod)`.
    fn bootstrap(&self) -> (ModDefId, ModDefId) {
        let primitives = DefinedPrimitives::create(self.env());
        let primitive_mod = self.make_primitive_mod(&primitives);
        self.primitives_or_unset().set(primitives).unwrap();

        let intrinsics = DefinedIntrinsics::create(*self.tc_env());
        let intrinsic_mod = self.make_intrinsic_mod(&intrinsics);
        self.intrinsics_or_unset().set(intrinsics).unwrap();

        (primitive_mod, intrinsic_mod)
    }

    /// Make a module containing all the intrinsics.
    fn make_intrinsic_mod(&self, intrinsics: &DefinedIntrinsics) -> ModDefId {
        self.mod_utils().create_mod_def(ModDefData {
            name: self.new_symbol("Intrinsics"),
            kind: ModKind::Transparent,
            members: self.mod_utils().create_mod_members(intrinsics.as_mod_members()),
        })
    }

    /// Make a module containing all the primitives.
    fn make_primitive_mod(&self, primitives: &DefinedPrimitives) -> ModDefId {
        self.mod_utils().create_mod_def(ModDefData {
            name: self.new_symbol("Primitives"),
            kind: ModKind::Transparent,
            members: self.mod_utils().create_mod_members(primitives.as_mod_members(self.env())),
        })
    }
}

impl<T: AccessToTcEnv> BootstrapOps for T {}
