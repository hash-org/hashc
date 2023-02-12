//! [`AtomInfoStore`] is a store that contains information about atoms in the
//! program, specifically their types.
use std::hash::Hash;

use hash_utils::store::{DefaultPartialStore, PartialCloneStore, PartialStore};

use super::{
    args::{ArgsId, PatArgsId},
    environment::env::AccessToEnv,
    params::ParamsId,
    pats::PatId,
    terms::TermId,
    tys::TyId,
};

/// Information about an atom in the program.
///
/// Atoms are terms, types, patterns, argument lists.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AtomInfo<Item: Copy, ItemTy: Copy> {
    /// The original data for this atom.
    ///
    /// The first member is the original item, the second member is the original
    /// type of the item if provided.
    original: (Item, Option<ItemTy>),
    /// The inferred data for this atom.
    ///
    /// If present, the first member is the inferred item, the second member is
    /// the inferred type of the item.
    inferred: Option<(Item, ItemTy)>,
}

impl<Item: Copy, ItemTy: Copy> AtomInfo<Item, ItemTy> {
    /// Create an empty atom info, only containing the original value.
    pub fn empty(original: Item) -> Self {
        Self { original: (original, None), inferred: None }
    }

    /// Create an atom info with the original value and type.
    pub fn with_original_ty(original: Item, original_ty: ItemTy) -> Self {
        Self { original: (original, Some(original_ty)), inferred: None }
    }
}

pub type AtomInfoStoreData<K, KT> = DefaultPartialStore<K, AtomInfo<K, KT>>;

/// Convenient trait to perform operations on [`AtomInfoStore`] for each key
/// type.
pub trait ItemInAtomInfo<Item: Copy + Eq + Hash, ItemTy: Copy>: AccessToEnv {
    fn data(&self) -> &AtomInfoStoreData<Item, ItemTy>;

    /// Create a new atom info with the given value.
    fn register_new_atom_without_ty(&self, value: Item) {
        self.data().insert(value, AtomInfo::empty(value));
    }

    /// Create a new atom info with the given value and type.
    fn register_new_atom(&self, value: Item, ty: ItemTy) {
        self.data().insert(value, AtomInfo::with_original_ty(value, ty));
    }

    /// Get the atom info for the given value, if it exists.
    fn try_get_atom_info(&self, value: Item) -> Option<AtomInfo<Item, ItemTy>> {
        self.data().get(value)
    }

    /// Get the inferred value for the given atom.
    fn try_get_inferred_value(&self, value: Item) -> Option<Item> {
        Some(self.data().get(value)?.inferred?.0)
    }

    /// Get the inferred type for the given atom.
    fn try_get_inferred_ty(&self, value: Item) -> Option<ItemTy> {
        Some(self.data().get(value)?.inferred?.1)
    }

    /// Get the inferred value for the given atom.
    ///
    /// This will panic if no inferred value is
    /// present.
    fn get_inferred_value(&self, value: Item) -> Item {
        self.data().get(value).unwrap().inferred.unwrap().0
    }

    /// Get the inferred type for the given atom.
    ///
    /// This will panic if no inferred type is
    /// present.
    fn get_inferred_ty(&self, value: Item) -> ItemTy {
        self.data().get(value).unwrap().inferred.unwrap().1
    }

    /// Get the atom info for the given value, or empty atom info if it doesn't.
    fn get_atom_info(&self, key: Item) -> AtomInfo<Item, ItemTy> {
        self.data().get(key).unwrap_or_else(|| AtomInfo::empty(key))
    }

    /// Register the inferred value and type, for the given value.
    fn register_atom_inference(&self, key: Item, inferred: Item, inferred_ty: ItemTy) {
        let is_present = self.data().modify_fast(key, |info| match info {
            Some(info) => {
                info.inferred = Some((inferred, inferred_ty));
                true
            }
            None => false,
        });
        if !is_present {
            // Add the original value and type, and the inferred value and
            // type.
            self.data().insert(
                key,
                AtomInfo { original: (key, None), inferred: Some((inferred, inferred_ty)) },
            );
        }

        if key != inferred {
            // Set the mapping from the inferred value to itself too.
            self.register_atom_inference(inferred, inferred, inferred_ty)
        }
    }
}
macro_rules! atom_info {
    ($($name:ident: <$item:ident, $item_ty:ty>),* $(,)?) => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq)]
        pub enum AtomInfoStoreItem {
            $(
                $item($item),
            )*
        }

        #[derive(Debug)]
        pub struct AtomInfoStore {
            $(
                pub $name: AtomInfoStoreData<$item, $item_ty>,
            )*
        }

        impl AtomInfoStore {
            pub fn new() -> Self {
                Self {
                    $(
                        $name: DefaultPartialStore::new(),
                    )*
                }
            }
        }

        impl Default for AtomInfoStore {
            fn default() -> Self {
                Self::new()
            }
        }

        $(
            impl<T: AccessToEnv> ItemInAtomInfo<$item, $item_ty> for T {
                fn data(&self) -> &AtomInfoStoreData<$item, $item_ty> {
                    &self.stores().atom_info().$name
                }
            }
        )*
    };
}

// Each stored atom, its value and its type:
atom_info! {
    terms: <TermId, TyId>,
    tys: <TyId, TyId>,
    pats: <PatId, TyId>,
    args: <ArgsId, ParamsId>,
    pat_args: <PatArgsId, ParamsId>,
}
