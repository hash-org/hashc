//! Defines a trait for representing ABI information about function, and
//! function arguments.

use std::cell::RefCell;

use hash_abi::{ArgAbi, FnAbi, FnAbiId};
use hash_ir::ty::InstanceId;
use hash_storage::store::{DefaultStore, Store, StoreInternalData};
use hash_utils::fxhash::FxHashMap;

use super::{layout::LayoutMethods, BackendTypes, HasCtxMethods};
use crate::lower::{abi::compute_fn_abi_from_instance, place::PlaceRef};

/// This trait defines functionality to construct the ABI of functions,
/// arguments, etc.
pub trait AbiBuilderMethods<'b>: HasCtxMethods<'b> + LayoutMethods<'b> + BackendTypes {
    /// Get a particular parameter from the ABI.
    fn get_param(&mut self, index: usize) -> Self::Value;

    /// Get the type of the provided [ArgAbi].
    fn arg_ty(&mut self, arg_abi: &ArgAbi) -> Self::Type;

    /// Store an argument that is passed or returned from a
    /// function call.
    fn store_fn_call_arg(
        &mut self,
        arg_abi: &ArgAbi,
        value: Self::Value,
        destination: PlaceRef<Self::Value>,
    );

    /// Specify that a particular function argument is to be
    /// stored in the specified [PlaceRef].
    fn store_fn_arg(
        &mut self,
        arg_abi: &ArgAbi,
        index: &mut usize,
        destination: PlaceRef<Self::Value>,
    );
}

/// Stores all of the created [FnAbi]s.
#[derive(Default)]
pub struct FnAbiStore {
    /// The store of all of the [FnAbi]s.
    store: DefaultStore<FnAbiId, FnAbi>,

    /// A mapping from [InstanceId] to [FnAbiId]. This is used to re-use results
    /// of computing ABIs from instances.
    instance_abi_map: RefCell<FxHashMap<InstanceId, FnAbiId>>,
}

impl Store<FnAbiId, FnAbi> for FnAbiStore {
    fn internal_data(&self) -> &StoreInternalData<FnAbi> {
        self.store.internal_data()
    }
}

impl FnAbiStore {
    /// Get the return ABI of a [FnAbiId].
    pub fn get_return_abi(&self, abi: FnAbiId) -> ArgAbi {
        self.map_fast(abi, |data| data.ret_abi)
    }

    /// Get the argument ABIs of a [FnAbiId] at the given index.
    pub fn get_arg_abi(&self, abi: FnAbiId, index: usize) -> ArgAbi {
        self.map_fast(abi, |data| data.args[index])
    }

    /// Create (or re-use) a [FnAbi] of the [InstanceId]. This function returns
    /// the [FnAbiId] of the [FnAbi] that was created.
    pub fn create_fn_abi<'b, Ctx>(&self, ctx: &Ctx, instance: InstanceId) -> FnAbiId
    where
        Ctx: HasCtxMethods<'b> + LayoutMethods<'b>,
    {
        if let Some(abi) = self.try_get_fn_abi(instance) {
            return abi;
        }

        // Create the ABI if it does not exist.
        let abi = self.store.create(
            // @@Todo: Emit a fatal error if the function ABI cannot be computed.
            compute_fn_abi_from_instance(ctx, instance).unwrap(),
        );

        // Add a mapping from the instance to the ABI.
        self.instance_abi_map.borrow_mut().insert(instance, abi);
        abi
    }

    /// Get the ABI of the [InstanceId] assuming that it has already
    /// been created.
    fn try_get_fn_abi(&self, instance: InstanceId) -> Option<FnAbiId> {
        self.instance_abi_map.borrow().get(&instance).copied()
    }

    /// Get the ABI of the [InstanceId] assuming that it has already
    /// been created.
    pub fn get_fn_abi(&self, instance: InstanceId) -> FnAbiId {
        self.try_get_fn_abi(instance).unwrap()
    }

    /// Get or create the ABI of the [InstanceId], and then map over the ABI.
    pub fn with_fn_abi<'b, F, R, Ctx>(&self, ctx: &mut Ctx, instance: InstanceId, f: F) -> R
    where
        F: FnOnce(&FnAbi, &mut Ctx) -> R,
        Ctx: HasCtxMethods<'b> + LayoutMethods<'b>,
    {
        // Get or create the ABI, and then map over it.
        let abi = self.create_fn_abi(ctx, instance);
        self.store.map_fast(abi, |abi| f(abi, ctx))
    }
}
