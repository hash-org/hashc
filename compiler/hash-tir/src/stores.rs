//! Defines the storage structures that contain TIR nodes,
//! as well as helper utilities to create these structures for different types
//! of nodes.
use std::sync::OnceLock;

use hash_storage::stores;

use crate::{
    atom_info::AtomInfoStore,
    stack::StackStore,
    tir::{
        blocks::{BlockStatementsSeqStore, BlockStatementsStore},
        ArgsSeqStore, ArgsStore, CtorDefsSeqStore, CtorDefsStore, DataDefStore, FnDefStore,
        LitStore, MatchCasesSeqStore, MatchCasesStore, ModDefStore, ModMembersSeqStore,
        ModMembersStore, ParamsSeqStore, ParamsStore, PatArgsSeqStore, PatArgsStore,
        PatListSeqStore, PatListStore, PatStore, SymbolStore, TermListSeqStore, TermListStore,
        TermStore,
    },
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
    lit: LitStore,
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
    match_cases: MatchCasesStore,
    match_cases_seq: MatchCasesSeqStore,
    block_statements: BlockStatementsStore,
    block_statements_seq: BlockStatementsSeqStore,
    atom_info: AtomInfoStore,
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
                use hash_storage::store::statics::StoreId;
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
                use hash_storage::store::statics::StoreId;
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
                use hash_storage::store::statics::StoreId;
                f.debug_tuple(stringify!($id)).field(&self.value().name).finish()
            }
        }
    };
}

/// Implement `NodeId` and `NodesId` for the given ID type.
#[macro_export]
macro_rules! impl_nodes_id {
    ($id:ty, $id_seq:ty) => {
        impl $crate::tir::NodesId for $id {
            type Elements = $id_seq;
            fn elements_node(&self) -> $crate::tir::Node<Self::Elements> {
                use hash_storage::store::statics::StoreId;
                self.value()
            }
        }
    };
}

/// Implement `NodeId` for the given ID type.
#[macro_export]
macro_rules! impl_node_id {
    ($id:ty) => {
        impl $crate::tir::NodeId for $id {
            fn origin(self) -> $crate::tir::NodeOrigin {
                use hash_storage::store::statics::StoreId;
                self.borrow().origin
            }
        }

        impl $crate::tir::HasAstNodeId for $id {
            fn node_id(&self) -> Option<hash_ast::ast::AstNodeId> {
                use hash_storage::store::statics::StoreId;
                self.value().node_id()
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
/// pub type TermId: StoreId<Value=Term>;
/// pub fn term_store() -> &'static TermStore;
/// ```
#[macro_export]
macro_rules! tir_node_single_store {
    // Generate the other names from the given `$name`:
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
    (
        store = $store_vis:vis $store:ident,
        id = $id_vis:vis $id:ident,
        value = $value:ty,
        store_name = $store_name:ident
    ) => {
        hash_storage::static_single_store!(
            store = $store_vis $store,
            id = $id_vis $id,
            value = $crate::tir::Node<$value>,
            store_name = $store_name,
            store_source = tir_stores()
        );
        $crate::tir_debug_value_of_single_store_id!($id);
        $crate::impl_node_id!($id);
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
/// pub type ParamsId: SingleStoreId<Value=Node<ParamsSeqId>>;
/// pub type ParamId: SingleStoreId<Value=Node<Param>>;
/// pub fn params_store() -> &'static ParamsStore;
/// pub fn params_seq_store() -> &'static ParamsSeqStore;
/// ```
///
/// What is the point of having `ParamsStore` as well as `ParamsSeqStore`?
/// `ParamsStore` maps `ParamsId` to the actual ID of the sequence,
/// `ParamsSeqId`, wrapped in a `Node`. This is so that the whole sequence has
/// an `origin` independently of whether or not it is empty (all empty sequences
/// in a sequence store share the same representation). `ParamsSeqStore` is the
/// actual sequence store, mapping a `ParamsSeqId` to a list of `Node<Param>`
/// values. This way, each element, as well as the sequence as a whole, has an
/// `origin`.
#[macro_export]
macro_rules! tir_node_sequence_store_direct {
    // Generate the other names from the given `$name`:
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
            value = $crate::tir::Node<$value>,
            store_name = $seq_store_name,
            store_source = tir_stores()
        );

        $crate::tir_debug_value_of_sequence_store_element_id!($el_id);
        $crate::impl_node_id!($el_id);
        $crate::impl_nodes_id!($id, $id_seq);

        /// The sequence wrapper key can act as a read-only key for the sequence store.
        impl hash_storage::store::sequence::SequenceStoreKey for $id {
            type ElementKey = $el_id;

            fn to_index_and_len(self) -> (usize, usize) {
                use $crate::tir::NodesId;
                self.elements().to_index_and_len()
            }

            unsafe fn from_index_and_len_unchecked(_: usize, _: usize) -> Self {
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
                use hash_storage::store::statics::StoreId;
                $el_id(value.0.value().data, value.1)
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
/// pub type TermListId: SingleStoreId<Value=Node<TermListSeqId>>;
/// pub type TermListSeqId: SequenceStoreId<Value=Vec<TermId>>;
/// pub fn term_list_store() -> &'static TermListStore;
/// pub fn term_list_seq_store() -> &'static TermListSeqStore;
/// ```
///
/// See `tir_node_sequence_store_direct!` for an explanation of the difference
/// between the sequence wrapper store and the sequence store itself. The
/// difference in this case is that the true sequence store does not wrap its
/// elements in a `Node` because it is expected that the elements themselves are
/// a TIR node ID which is already mapped to a `Node` in another store.
#[macro_export]
macro_rules! tir_node_sequence_store_indirect {
    // Generate the other names from the given `$name_s` for the sequence and `$element` for the
    // element:
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
        // Create the sequence wrapper store (needed to wrap each sequence in a Node<..>):
        $crate::tir_node_single_store!(
            store = $store_vis $store,
            id = $id_vis $id,
            value = $id_seq,
            store_name = $store_name
        );

        // Create the sequence store itself:
        hash_storage::static_sequence_store_indirect!(
            store = $store_vis $seq_store,
            id = $id_vis $id_seq[$el_id],
            store_name = $seq_store_name,
            store_source = tir_stores()
        );
        $crate::impl_nodes_id!($id, $id_seq);

        /// The sequence wrapper key can act as a read-only key for the sequence store.
        impl hash_storage::store::sequence::SequenceStoreKey for $id {
            type ElementKey = $el_id;

            fn to_index_and_len(self) -> (usize, usize) {
                use $crate::tir::NodesId;
                self.elements().to_index_and_len()
            }

            unsafe fn from_index_and_len_unchecked(_: usize, _: usize) -> Self {
                panic!(
                    "{} cannot be used to create a new sequence, use {} instead",
                    stringify!($id),
                    stringify!($id_seq)
                )
            }
        }

        impl From<($id, usize)> for $el_id {
            fn from(value: ($id, usize)) -> Self {
                use hash_storage::store::statics::StoreId;
                value.0.borrow().at(value.1).unwrap()
            }
        }
    };
}
