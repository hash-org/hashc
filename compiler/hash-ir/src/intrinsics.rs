//! Defines all of the intrinsics that are expected to be
//! declared within the language prelude.

use hash_utils::store::{SequenceStore, Store};

use crate::ty::{Instance, InstanceStore, IrTy, IrTyId, TyStore};

/// Defines all of the intrinsics that are present within the
/// language runtime, and can be accessed by the language. This
/// does not capture "all" intrinsics since some are defined
/// at the backend level and might not be generally available.
/// The [Intrinsic] items are intrinsics that are required by the
/// language to provide functionality that cannot be provided
/// by the runtime itself, i.e. "panic".
///
/// @@Todo: this needs to record the number of arguments the intrinsic
/// takes, and possibly other information.
///
/// More specifically, the prelude should have a way of marking the
/// function as an intrinsic within the `Intrinsic` module, which then
/// directly references these language items. This then allows for the
/// program to reference the intrinsic implementation.
///
/// For now, we just create the function type, and then use it to generate
/// the intrinsic function.
pub enum Intrinsic {
    /// The `panic` intrinsic function. This will cause the program
    /// to terminate.
    Panic,
}

impl Intrinsic {
    /// Get the appropriate [Intrinsic] for the specified name.
    pub fn from_str_name(name: &str) -> Self {
        match name {
            "panic" => Self::Panic,
            _ => panic!("unknown intrinsic: {name}"),
        }
    }
}

/// This struct is used to map the [Intrinsic] enum to the
/// associated type that is used to represent the intrinsic.
#[derive(Default)]
pub struct Intrinsics {
    /// The intrinsic map.
    intrinsics: [Option<IrTyId>; std::mem::variant_count::<Intrinsic>()],
}

impl Intrinsics {
    /// Create a new [Intrinsics] map instance. This will create
    /// all the associated types for the intrinsics, and will populate
    /// the map with them.
    pub fn new(tys: &TyStore, instances: &InstanceStore) -> Self {
        let mut intrinsics = [None; std::mem::variant_count::<Intrinsic>()];

        // @@Temp: the intrinsics should be tracked using DefIds in order
        // so that we can properly deduce the source-id of the defined place.
        // For now, we just don't set a source_id for these.

        macro_rules! define_intrinsic {
            ($name:literal, fn() -> $ret:expr) => (
                let params = tys.tls.create_empty();
                let instance = instances.create(Instance::new(
                    $name.into(),
                    None,
                    params,
                    $ret,
                ));

                intrinsics[Intrinsic::from_str_name($name) as usize] = Some(tys.create(IrTy::Fn {
                    params,
                    return_ty: $ret,
                    instance
                }));
            );
            ($name:literal, fn($($arg:expr),*) -> $ret:expr) => (
                let params = tys.tls.create_from_slice(&[$($arg),*]);
                let instance = instances.create(
                    Instance::new(
                        $name.into(),
                        None,
                        params,
                        $ret,
                    )
                );

                intrinsics[Intrinsic::from_str_name($name) as usize] = Some(tys.create(IrTy::Fn {
                    params,
                    return_ty: $ret,
                    instance
                }));
            );
        }

        let str_ty = tys.common_tys.str;
        let never_ty = tys.common_tys.never;

        // @@Temporary: define the intrinsics using this macro, however we should
        // be able to specify these intrinsics in the prelude.
        define_intrinsic!("panic", fn(str_ty) -> never_ty);

        Self { intrinsics }
    }

    /// Set the [IrTyId] for the specified intrinsic.
    pub fn set(&mut self, intrinsic: Intrinsic, ty: IrTyId) {
        self.intrinsics[intrinsic as usize] = Some(ty);
    }

    /// Get the [IrTyId] for the specified intrinsic.
    pub fn get(&self, intrinsic: Intrinsic) -> Option<IrTyId> {
        self.intrinsics[intrinsic as usize]
    }
}
