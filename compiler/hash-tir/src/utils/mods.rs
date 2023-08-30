//! Module-related utilities.
use derive_more::Constructor;
use hash_ast::ast::OwnsAstNode;
use hash_source::{identifier::Identifier, ModuleId};
use hash_storage::store::statics::SequenceStoreValue;

use crate::{
    environment::{
        env::{AccessToEnv, Env},
        stores::tir_stores,
    },
    impl_access_to_env,
    mods::{ModDef, ModDefId, ModKind, ModMember},
    node::{Node, NodeOrigin},
    symbols::Symbol,
};

/// Operations related to module definitions.
#[derive(Constructor)]
pub struct ModUtils<'tc> {
    env: &'tc Env<'tc>,
}

impl_access_to_env!(ModUtils<'tc>);

impl<'tc> ModUtils<'tc> {
    /// Create or get an existing module definition by `[SourceId]`.
    pub fn create_or_get_module_mod_def(&self, module_id: ModuleId) -> ModDefId {
        let source_node_id = self.node_map().get_module(module_id).node_ref().id();
        match tir_stores().ast_info().mod_defs().get_data_by_node(source_node_id) {
            Some(existing) => existing,
            None => {
                // Create a new module definition.
                let source_id = module_id.into();
                let module_name: Identifier = self.source_map().source_name(source_id).into();
                let mod_def_id = Node::create_at(
                    ModDef {
                        name: Symbol::from_name(module_name),
                        kind: ModKind::Source(
                            source_id,
                            // @@Hack: leak the path to still allow ModKind to implement Copy.
                            // We need the path inside ModKind so that we can print it without
                            // requiring access to source map. Ideally SourceMap should be static
                            // so that this is not needed.
                            Box::leak(
                                self.source_map()
                                    .source_path(source_id)
                                    .to_path_buf()
                                    .into_boxed_path(),
                            ),
                        ),
                        members: Node::create_at(
                            Node::<ModMember>::empty_seq(),
                            NodeOrigin::Generated,
                        ),
                    },
                    NodeOrigin::Generated,
                );
                tir_stores().ast_info().mod_defs().insert(source_node_id, mod_def_id);
                mod_def_id
            }
        }
    }
}
