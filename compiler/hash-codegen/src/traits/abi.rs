//! Defines a trait for representing ABI information about function, and
//! function arguments.

use std::cell::RefCell;

use hash_abi::{ArgAbi, CallingConvention, FnAbi, FnAbiId};
use hash_ir::ty::{FnTy, InstanceId, ReprTy, ReprTyId};
use hash_storage::store::{DefaultStore, Store, StoreInternalData, statics::StoreId};
use hash_utils::fxhash::FxHashMap;

use super::{BackendTypes, HasCtxMethods, layout::LayoutMethods};
use crate::lower::{
    abi::{compute_fn_abi, compute_fn_abi_from_instance},
    place::PlaceRef,
};

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
    pub fn create_fn_abi_from_instance<'b, Ctx>(
        &self,
        ctx: &Ctx,
        ty: ReprTyId,
        instance: InstanceId,
    ) -> FnAbiId
    where
        Ctx: HasCtxMethods<'b> + LayoutMethods<'b>,
    {
        if let Some(abi) = self.try_get_fn_abi(instance) {
            return abi;
        }

        // Create the ABI if it does not exist.
        let abi = self.store.create(
            // @@Todo: Emit a fatal error if the function ABI cannot be computed.
            compute_fn_abi_from_instance(ctx, ty, instance).unwrap(),
        );

        // Add a mapping from the instance to the ABI.
        self.instance_abi_map.borrow_mut().insert(instance, abi);
        abi
    }

    /// Compute the [FnAbi] of a given [FnTy] assuming that it is the standard
    /// calling convention of the target.
    pub fn create_fn_abi_from_ty<'b, Ctx>(&self, ctx: &Ctx, ty: ReprTyId) -> FnAbiId
    where
        Ctx: HasCtxMethods<'b> + LayoutMethods<'b>,
    {
        let ty_info = ty.value();
        let FnTy { params, return_ty } = match ty_info {
            ReprTy::FnDef { instance } => {
                return self.create_fn_abi_from_instance(ctx, ty, instance);
            }
            ReprTy::Fn(func) => func,
            _ => unreachable!(),
        };

        // @@Todo: do we need to configure it based on any func attrs?
        let calling_convention = CallingConvention::C;

        self.store.create(
            // @@Todo: Emit a fatal error if the function ABI cannot be computed.
            compute_fn_abi(ctx, ty, params, return_ty, calling_convention).unwrap(),
        )
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
}
