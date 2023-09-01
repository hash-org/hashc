use std::sync::OnceLock;

use hash_storage::stores;

use crate::{
    args::{ArgsSeqStore, ArgsStore, PatArgsSeqStore, PatArgsStore},
    ast_info::AstInfo,
    atom_info::AtomInfoStore,
    control::{MatchCasesSeqStore, MatchCasesStore},
    data::{CtorDefsSeqStore, CtorDefsStore, DataDefStore},
    fns::FnDefStore,
    locations::LocationStore,
    mods::{ModDefStore, ModMembersSeqStore, ModMembersStore},
    params::{ParamsSeqStore, ParamsStore},
    pats::{PatListSeqStore, PatListStore, PatStore},
    scopes::StackStore,
    symbols::SymbolStore,
    terms::{TermListSeqStore, TermListStore, TermStore},
    tys::TyStore,
};

// All the stores that contain definitions for the typechecker.
//
// Each store created by the `tir_node_store_*` macros below must be registered
// here.
stores! {
    Stores;
    args: ArgsStore,
    args_seq: ArgsSeqStore,
    ctor_defs: CtorDefsStore,
    ctor_defs_seq: CtorDefsSeqStore,
    data_def: DataDefStore,
    fn_def: FnDefStore,
    location: LocationStore,
    mod_def: ModDefStore,
    mod_members: ModMembersStore,
    mod_members_seq: ModMembersSeqStore,
    params: ParamsStore,
    params_seq: ParamsSeqStore,
    pat: PatStore,
    pat_args: PatArgsStore,
    pat_args_seq: PatArgsSeqStore,
    pat_list: PatListStore,
    pat_list_seq: PatListSeqStore,
    stack: StackStore,
    symbol: SymbolStore,
    term: TermStore,
    term_list: TermListStore,
    term_list_seq: TermListSeqStore,
    ty: TyStore,
    match_cases: MatchCasesStore,
    match_cases_seq: MatchCasesSeqStore,
    atom_info: AtomInfoStore,
    ast_info: AstInfo,
}

/// The global [`Stores`] instance.
static STORES: OnceLock<Stores> = OnceLock::new();

/// Access the global [`Stores`] instance.
pub fn tir_stores() -> &'static Stores {
    STORES.get_or_init(Stores::new)
}

// Below are some helper macros for defining TIR nodes:

/// Debug a sequence store element by printing its index and length, as well as
/// its value.
#[macro_export]
macro_rules! tir_debug_value_of_sequence_store_element_id {
    ($id:ident) => {
        impl std::fmt::Debug for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                use hash_storage::store::statics::CoreStoreId;
                f.debug_tuple(stringify!($id))
                    .field(&(&self.0.index, &self.0.len))
                    .field(&self.1)
                    .field(&self.value())
                    .finish()
            }
        }
    };
}

/// Debug a store ID by printing its index and value.
#[macro_export]
macro_rules! tir_debug_value_of_single_store_id {
    ($id:ident) => {
        impl std::fmt::Debug for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                use hash_storage::store::statics::CoreStoreId;
                f.debug_tuple(stringify!($id)).field(&self.index).field(&self.value()).finish()
            }
        }
    };
}

/// Debug any store element by only printing its name (element values must have
/// a field `.main`).
#[macro_export]
macro_rules! tir_debug_name_of_store_id {
    ($id:ident) => {
        impl std::fmt::Debug for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                use hash_storage::store::statics::CoreStoreId;
                f.debug_tuple(stringify!($id)).field(&self.value().name).finish()
            }
        }
    };
}

/// Define a TIR node that is stored in a single store.
///
/// This internally uses `hash_storage::static_single_store!` to define the
/// store and its ID type; it creates a single store with values
/// `Node<$value>`.
///
/// This can be used to define TIR nodes like:
///
/// ```ignore
/// tir_node_single_store!(Term);
///
/// /// These now exist:
/// pub type TermStore: Store<TermId, Node<Term>>;
/// pub type TermId: CoreStoreId<Value=Term>;
/// pub fn term_store() -> &'static TermStore;
/// ```
#[macro_export]
macro_rules! tir_node_single_store {
    // Using the given name, define a TIR node that is stored in a single store, generating the
    // other names.
    ($name:ident) => {
        paste::paste! {
            tir_node_single_store!(
                store = pub [<$name:camel Store>],
                id = pub [<$name:camel Id>],
                value = $name,
                store_name = [<$name:snake>]
            );
        }
    };
    // Using the given names, define a TIR node that is stored in a single
    // store.
    (
        store = $store_vis:vis $store:ident,
        id = $id_vis:vis $id:ident,
        value = $value:ty,
        store_name = $store_name:ident
    ) => {
        hash_storage::static_single_store!(
            store = $store_vis $store,
            id = $id_vis $id,
            value = $crate::node::Node<$value>,
            store_name = $store_name,
            store_source = tir_stores()
        );
        $crate::tir_debug_value_of_single_store_id!($id);

        // @@Todo: enable once locations are properly set up
        // impl $crate::ast_info::HasNodeId for $id {
        //     fn node_id(&self) -> Option<hash_ast::ast::AstNodeId> {
        //         self.value().node_id()
        //     }
        // }
    };
}

/// Define a TIR node that is stored in a direct sequence store.
///
/// This internally uses `hash_storage::static_single_store!` and
/// `hash_storage::static_sequence_store_direct!` to define the store and its ID
/// type; it creates a single store from key `$id` to value `Node<$id_seq>`, and
/// a direct sequence store from key `$id_seq` to values in `$value`.
///
/// This can be used to define TIR nodes like:
///
/// ```ignore
/// tir_node_sequence_store_direct!(Param);
///
/// /// These now exist:
/// pub type ParamsStore: Store<ParamsId, Node<ParamsSeqId>>;
/// pub type ParamsSeqStore: SequenceStore<ParamsSeqId, Node<Param>>;
/// pub type ParamsSeqId: SequenceStoreId<Value=Vec<Node<Param>>>;
/// pub type ParamsId: StoreId<Value=Node<ParamsSeqId>>;
/// pub type ParamId: StoreId<Value=Node<Param>>;
/// pub fn params_store() -> &'static ParamsStore;
/// pub fn params_seq_store() -> &'static ParamsSeqStore;
/// ```
#[macro_export]
macro_rules! tir_node_sequence_store_direct {
    ($name:ident) => {
        paste::paste! {
            tir_node_sequence_store_direct!(
                store = pub [<$name:camel sStore>] -> [<$name:camel sSeqStore>],
                id = pub [<$name:camel sId>] -> [<$name:camel sSeqId>][[<$name:camel Id>]],
                value = $name,
                store_name = ([<$name:snake s>], [<$name:snake s_seq>])
            );
        }
    };
    (
        store = $store_vis:vis $store:ident -> $seq_store:ident,
        id = $id_vis:vis $id:ident -> $id_seq:ident[$el_id:ident],
        value = $value:ty,
        store_name = ($store_name:ident, $seq_store_name:ident)
    ) => {
        // Create the sequence wrapper store (needed to wrap each sequence in a Node<..>):
        $crate::tir_node_single_store!(
            store = $store_vis $store,
            id = $id_vis $id,
            value = $id_seq,
            store_name = $store_name
        );

        // Create the sequence store itself:
        hash_storage::static_sequence_store_direct!(
            store = $store_vis $seq_store,
            id = $id_vis $id_seq[$el_id],
            value = $crate::node::Node<$value>,
            store_name = $seq_store_name,
            store_source = tir_stores()
        );

        $crate::tir_debug_value_of_sequence_store_element_id!($el_id);

        /// The sequence wrapper key can act as a read-only key for the sequence store.
        impl hash_storage::store::sequence::SequenceStoreKey for $id {
            type ElementKey = $el_id;

            fn to_index_and_len(self) -> (usize, usize) {
                use hash_storage::store::statics::CoreStoreId;
                self.value().to_index_and_len()
            }

            fn from_index_and_len_unchecked(_: usize, _: usize) -> Self {
                panic!(
                    "{} cannot be used to create a new sequence, use {} instead",
                    stringify!($id),
                    stringify!($id_seq)
                )
            }
        }

        /// Needed for the `SequenceStoreKey` impl.
        impl From<($id, usize)> for $el_id {
            fn from(value: ($id, usize)) -> Self {
                use hash_storage::store::statics::CoreStoreId;
                $el_id(value.0.value().data, value.1)
            }
        }

        impl $id {
            /// Access the elements of this sequence wrapper.
            pub fn elements(self) -> $id_seq {
                *self.value()
            }
        }
    };
}

/// Define a TIR node that is stored in an indirect sequence store.
///
/// This internally uses `hash_storage::static_single_store!` and
/// `hash_storage::static_sequence_store_indirect!` to define the store and its
/// ID type; it creates a single store from key `$id` to value `Node<$id_seq>`,
/// and an indirect sequence store containing `$el_id`.
///
/// This can be used to define TIR nodes like:
///
/// ```ignore
/// tir_node_sequence_store_indirect!(TermList[TermId]);
///
/// /// These now exist:
/// pub type TermListStore: Store<TermListId, Node<TermListSeqId>>;
/// pub type TermListSeqStore: SequenceStore<TermListSeqId, TermId>;
/// pub type TermListId: StoreId<Value=Node<TermListSeqId>>;
/// pub type TermListSeqId: SequenceStoreId<Value=Vec<TermId>>;
/// pub fn term_list_store() -> &'static TermListStore;
/// pub fn term_list_seq_store() -> &'static TermListSeqStore;
/// ```
#[macro_export]
macro_rules! tir_node_sequence_store_indirect {
    ($name_s:ident[$element:ty]) => {
        paste::paste! {
            tir_node_sequence_store_indirect!(
                store = pub [<$name_s:camel Store>] -> [<$name_s:camel SeqStore>],
                id = pub [<$name_s:camel Id>] -> [<$name_s:camel SeqId>][[<$element>]],
                store_name = ([<$name_s:snake>], [<$name_s:snake _seq>])
            );
        }
    };
    (
        store = $store_vis:vis $store:ident -> $seq_store:ident,
        id = $id_vis:vis $id:ident -> $id_seq:ident[$el_id:ident],
        store_name = ($store_name:ident, $seq_store_name:ident)
    ) => {
        $crate::tir_node_single_store!(
            store = $store_vis $store,
            id = $id_vis $id,
            value = $id_seq,
            store_name = $store_name
        );

        hash_storage::static_sequence_store_indirect!(
            store = $store_vis $seq_store,
            id = $id_vis $id_seq[$el_id],
            store_name = $seq_store_name,
            store_source = tir_stores()
        );

        impl hash_storage::store::sequence::SequenceStoreKey for $id {
            type ElementKey = $el_id;

            fn to_index_and_len(self) -> (usize, usize) {
                use hash_storage::store::statics::CoreStoreId;
                self.value().to_index_and_len()
            }

            fn from_index_and_len_unchecked(_: usize, _: usize) -> Self {
                panic!(
                    "{} cannot be used to create a new sequence, use {} instead",
                    stringify!($id),
                    stringify!($id_seq)
                )
            }
        }

        impl From<($id, usize)> for $el_id {
            fn from(value: ($id, usize)) -> Self {
                use hash_storage::store::statics::CoreStoreId;
                value.0.borrow().at(value.1).unwrap()
            }
        }
    };
}
