//! Bootstrap the typechecker, by creating and injecting primitive definitions
//! into the context.

use derive_more::Constructor;
use hash_intrinsics::{intrinsics::DefinedIntrinsics, primitives::DefinedPrimitives};
use hash_tir::new::{
    environment::env::AccessToEnv,
    mods::{ModDefData, ModDefId, ModKind},
    utils::{common::CommonUtils, AccessToUtils},
};
use once_cell::unsync::OnceCell;

use crate::{
    impl_access_to_tc_env,
    new::environment::tc_env::{AccessToTcEnv, TcEnv},
};

#[derive(Constructor)]
pub struct BootstrapOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

pub type DefinedPrimitivesOrUnset = OnceCell<DefinedPrimitives>;
pub type DefinedIntrinsicsOrUnset = OnceCell<DefinedIntrinsics>;

impl_access_to_tc_env!(BootstrapOps<'tc>);

impl<'tc> BootstrapOps<'tc> {
    /// Bootstrap the typechecker, by constructing primitives and intrinsics,
    /// then creating modules of the two and giving them to
    /// the provided closure.
    pub fn bootstrap<T>(&self, f: impl FnOnce(ModDefId) -> T) -> T {
        let primitives = DefinedPrimitives::create(self.env());
        self.primitives_or_unset().set(primitives).unwrap();
        let intrinsics = DefinedIntrinsics::create(*self.tc_env());
        self.intrinsics_or_unset().set(intrinsics).unwrap();

        let primitive_mod = self.make_primitive_mod(&primitives);
        f(primitive_mod)
    }

    /// From the given [`DefinedPrimitives`], create a module that contains
    /// them as members.
    pub fn make_primitive_mod(&self, primitives: &DefinedPrimitives) -> ModDefId {
        self.mod_utils().create_mod_def(ModDefData {
            name: self.new_symbol("Primitives"),
            kind: ModKind::Transparent,
            members: self.mod_utils().create_mod_members(primitives.as_mod_members(self.env())),
        })
    }
}
