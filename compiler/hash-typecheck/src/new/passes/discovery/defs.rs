//! Utilities for keeping track of definitions during the discovery pass.
use derive_more::From;
use hash_ast::ast::{self, AstNode, AstNodeId, AstNodeRef};
use hash_reporting::macros::panic_on_span;
use hash_types::new::{
    data::{CtorDefData, DataDefId},
    defs::DefId,
    environment::env::AccessToEnv,
    mods::{ModDefId, ModMemberData, ModMemberValue},
    scopes::{StackId, StackMemberData},
    symbols::Symbol,
    tys::TyId,
};
use hash_utils::{
    state::LightState,
    store::{DefaultPartialStore, PartialStore, SequenceStoreKey, Store},
};
use smallvec::{smallvec, SmallVec};

use super::{super::ast_utils::AstUtils, DiscoveryPass};
use crate::new::{
    environment::tc_env::AccessToTcEnv,
    ops::{common::CommonOps, AccessToOps},
};

/// An item that is discovered: either a definition or a function type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, From)]
pub(super) enum ItemId {
    Def(DefId),
    FnTy(TyId),
}

/// Contains information about seen definitions, members of definitions, as well
/// as the "current" definition we are in. Also holds a name hint so that
/// declarations like `X := mod {}` can be given the name `X`.
#[derive(Debug, Default)]
pub(super) struct DefDiscoveryState {
    /// The current definition we are in.
    currently_in: LightState<Option<ItemId>>,
    /// The mod member we have seen, indexed by the mod ID.
    mod_members: DefaultPartialStore<ModDefId, Vec<(AstNodeId, ModMemberData)>>,
    /// The data ctor we have seen, indexed by the data definition ID.
    data_ctors: DefaultPartialStore<DataDefId, Vec<(AstNodeId, CtorDefData)>>,
    /// The stack members we have seen, indexed by the stack ID.
    stack_members: DefaultPartialStore<StackId, Vec<(AstNodeId, StackMemberData)>>,
}

impl DefDiscoveryState {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'tc> DiscoveryPass<'tc> {
    /// Run the given closure with the given item as "current", resetting
    /// it at the end. It does not handle definition members.
    ///
    /// This will add the definition to the originating node in `ast_info`. The
    /// originating node is the node that represents the definition, e.g.
    /// the `mod` node for `X := mod {...}`.
    pub(super) fn enter_item<T, U>(
        &self,
        originating_node: AstNodeRef<U>,
        def_id: impl Into<ItemId>,
        f: impl FnOnce() -> T,
    ) -> T {
        let def_id = def_id.into();

        // Add the definition to the originating node.
        self.add_def_to_ast_info(def_id, originating_node);

        self.def_state().currently_in.enter(Some(def_id), f)
    }

    /// Run the given closure with the given definition as "current", resetting
    /// it at the end.
    ///
    /// This will add found sub-definitions/members to the entered definition
    /// after exiting, if applicable. It will also add the definition to the
    /// originating node in `ast_info`. The originating node is the node that
    /// represents the definition, e.g. the `mod` node for `X := mod {...}`.
    pub(super) fn enter_def<T, U>(
        &self,
        originating_node: AstNodeRef<U>,
        def_id: impl Into<DefId>,
        f: impl FnOnce() -> T,
    ) -> T {
        let def_id = def_id.into();

        // Add the definition to the member context.
        match def_id {
            DefId::Mod(id) => {
                self.def_state().mod_members.insert(id, vec![]);
            }
            DefId::Data(id) => {
                self.def_state().data_ctors.insert(id, vec![]);
            }
            DefId::Stack(id) => {
                self.def_state().stack_members.insert(id, vec![]);
            }
            DefId::Fn(_) => {}
        }

        let result = self.enter_item(originating_node, ItemId::Def(def_id), f);

        // Add the found members to the definition.
        self.add_found_members_to_def(def_id);

        // Add location information to the definition.
        self.add_node_location_to_def(def_id, originating_node);

        result
    }

    /// Get the "current" definition, or panic if there is none.
    pub(super) fn get_current_item(&self) -> ItemId {
        self.def_state()
            .currently_in
            .get()
            .unwrap_or_else(|| panic!("Tried to get def but none was set"))
    }

    /// Add the given definition to the AST info of the given node.
    pub(super) fn add_def_to_ast_info<U>(&self, item_id: ItemId, node: AstNodeRef<U>) {
        // @@Todo: add locations of params from somewhere
        let ast_info = self.ast_info();
        match item_id {
            ItemId::Def(def_id) => match def_id {
                DefId::Mod(id) => ast_info.mod_defs().insert(node.id(), id),
                DefId::Data(id) => ast_info.data_defs().insert(node.id(), id),
                DefId::Fn(id) => ast_info.fn_defs().insert(node.id(), id),
                DefId::Stack(id) => ast_info.stacks().insert(node.id(), id),
            },
            ItemId::FnTy(id) => ast_info.tys().insert(node.id(), id),
        };
    }

    /// Add the found members of the given definitions to the definitions
    /// themselves, as well as to the `ast_info` stores.
    ///
    /// We store a tuple `(AstNodeId, MemberData)` for each member we find in
    /// the scope discovery. Therefore, we first create a `Member` from the
    /// `MemberData` and then using its `MemberId` and `AstNodeId` we add it to
    /// `AstInfo` store, appropriately depending on the definition kind,
    pub(super) fn add_found_members_to_def(&self, def_id: impl Into<DefId>) {
        let ast_info = self.ast_info();
        match def_id.into() {
            DefId::Mod(mod_def_id) => {
                self.def_state().mod_members.modify_fast(mod_def_id, |members| {
                    if let Some(members) = members {
                        let members = std::mem::take(members);
                        let mod_ops = self.mod_ops();

                        // Set module members.
                        let mod_members = mod_ops.set_mod_def_members(
                            mod_def_id,
                            mod_ops
                                .create_mod_members(members.iter().map(|(_, data)| data).cloned()),
                        );

                        // Set node for each member.
                        for ((node_id, _), mod_member_index) in
                            members.iter().zip(mod_members.to_index_range())
                        {
                            ast_info
                                .mod_members()
                                .insert(*node_id, (mod_members, mod_member_index));
                        }
                    }
                })
            }
            DefId::Data(data_def_id) => {
                self.def_state().data_ctors.modify_fast(data_def_id, |members| {
                    if let Some(members) = members {
                        let members = std::mem::take(members);
                        let data_ops = self.data_ops();

                        // Set data constructors.
                        let data_members = data_ops.set_data_def_ctors(
                            data_def_id,
                            data_ops.create_data_ctors(
                                data_def_id,
                                members.iter().map(|(_, data)| data).copied(),
                            ),
                        );

                        // Set node for each data constructor.
                        for ((node_id, _), data_ctor_index) in
                            members.iter().zip(data_members.to_index_range())
                        {
                            ast_info.ctor_defs().insert(*node_id, (data_members, data_ctor_index));
                        }
                    }
                })
            }
            DefId::Fn(_) => {
                // Nothing to do here, functions don't have members.
            }
            DefId::Stack(stack_id) => {
                self.def_state().stack_members.modify_fast(stack_id, |members| {
                    if let Some(members) = members {
                        let members = std::mem::take(members);
                        let members_len = members.len();
                        let stack_ops = self.stack_ops();

                        // Set stack members.
                        stack_ops.set_stack_members(
                            stack_id,
                            stack_ops.create_stack_members(
                                stack_id,
                                members.iter().map(|(_, data)| data).copied(),
                            ),
                        );

                        // Set node for each stack member.
                        for ((node_id, _), member_index) in members.iter().zip(0..members_len) {
                            ast_info.stack_members().insert(*node_id, (stack_id, member_index));
                        }
                    }
                })
            }
        }
    }

    /// Add a declaration node `a := b` to the given `mod_def_id` (which is
    /// "current").
    ///
    /// This will add the appropriate `MemberData` to the `mod_members` local
    /// score. In other words, a tuple `(AstNodeId, ModMemberData)`. The
    /// `ModMemberData` is found by looking at the `ast_info` of the value of
    /// the declaration, which denotes if the value is a resolved
    /// module/function/data definition etc. If the value is not resolved, then
    /// it is not a valid module member.
    pub(super) fn add_declaration_node_to_mod_def(
        &self,
        node: AstNodeRef<ast::Declaration>,
        mod_def_id: ModDefId,
    ) {
        // The `def_node_id` is the `AstNodeId` of the actual definition value that
        // this declaration is pointing to. For example, in `Y := mod {...}`, the `mod`
        // node's ID (which is a block) would be `def_node_id`.
        let def_node_id = match node.value.as_ref().map(|node| node.body()) {
            // If the declaration is a block, we need to get the
            // right node to look up the members
            Some(ast::Expr::Block(block)) => block.data.id(),
            Some(_) => node.value.as_ref().unwrap().id(),
            _ => {
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "Found declaration without value"
                )
            }
        };

        let ast_info = self.ast_info();
        self.def_state().mod_members.modify_fast(mod_def_id, |members| {
            let members = match members {
                Some(members) => members,
                None => {
                    panic!("Got empty members for mod def {mod_def_id:?}");
                }
            };

            if let Some(fn_def_id) = ast_info.fn_defs().get_data_by_node(def_node_id) {
                // Function definition in a module
                self.stores().fn_def().map_fast(fn_def_id, |fn_def| {
                    members.push((
                        node.id(),
                        ModMemberData { name: fn_def.name, value: ModMemberValue::Fn(fn_def_id) },
                    ));
                })
            } else if let Some(data_def_id) = ast_info.data_defs().get_data_by_node(def_node_id) {
                // Data definition in a module
                self.stores().data_def().map_fast(data_def_id, |data_def| {
                    members.push((
                        node.id(),
                        ModMemberData {
                            name: data_def.name,
                            value: ModMemberValue::Data(data_def_id),
                        },
                    ));
                })
            } else if let Some(nested_mod_def_id) =
                ast_info.mod_defs().get_data_by_node(def_node_id)
            {
                // Nested module in a module
                self.stores().mod_def().map_fast(nested_mod_def_id, |nested_mod_def| {
                    members.push((
                        node.id(),
                        ModMemberData {
                            name: nested_mod_def.name,
                            value: ModMemberValue::Mod(nested_mod_def_id),
                        },
                    ));
                })
            } else if ast_info.stacks().get_data_by_node(def_node_id).is_some() {
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "Found stack member in mod definition"
                )
            } else {
                // Unknown definition, do nothing
                //
                // Here we don't panic because there might have been a
                // recoverable error in a declaration which could have led to no
                // `AstInfo` being recorded, for example for
                // `TraitsNotSupported` error.
            }
        });
    }

    /// Create and add `StackMemberData` values to the given `buf`, from the
    /// given pattern `node`.
    ///
    /// This recursively adds all the bindings of the pattern as stack members.
    /// It leaves types as holes and values as `None`, because they will be
    /// resolved at a later stage.
    pub(super) fn add_stack_members_in_pat_to_buf(
        &self,
        node: AstNodeRef<ast::Pat>,
        buf: &mut SmallVec<[(AstNodeId, StackMemberData); 3]>,
    ) {
        let register_spread_pat =
            |spread: &AstNode<ast::SpreadPat>,
             buf: &mut SmallVec<[(AstNodeId, StackMemberData); 3]>| {
                if let Some(name) = &spread.name {
                    buf.push((
                        node.id(),
                        StackMemberData {
                            name: self.new_symbol(name.ident),
                            is_mutable: false,
                            ty: self.new_ty_hole(),
                            value: None,
                        },
                    ))
                }
            };

        match node.body() {
            ast::Pat::Binding(binding) => {
                buf.push((
                    node.id(),
                    StackMemberData {
                        name: self.new_symbol(binding.name.ident),
                        is_mutable: binding.mutability.as_ref().map(|m| *m.body())
                            == Some(ast::Mutability::Mutable),
                        ty: self.new_ty_hole(),
                        value: None,
                    },
                ));
            }
            ast::Pat::Module(_) => {
                // This should have been handled pre-tc semantics
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "Found module pattern in stack definition"
                )
            }
            ast::Pat::Tuple(ast::TuplePat { fields, spread }) => {
                for (index, field) in fields.ast_ref_iter().enumerate() {
                    if let Some(spread_node) = &spread && spread_node.position == index {
                        register_spread_pat(spread_node, buf);
                    }

                    self.add_stack_members_in_pat_to_buf(field.pat.ast_ref(), buf);
                }
            }
            ast::Pat::Constructor(ast::ConstructorPat { fields, spread, .. }) => {
                for (index, field) in fields.ast_ref_iter().enumerate() {
                    if let Some(spread_node) = &spread && spread_node.position == index {
                        register_spread_pat(spread_node, buf);
                    }

                    self.add_stack_members_in_pat_to_buf(field.pat.ast_ref(), buf);
                }
            }
            ast::Pat::List(ast::ListPat { fields, spread }) => {
                for (index, field) in fields.ast_ref_iter().enumerate() {
                    if let Some(spread_node) = &spread && spread_node.position == index {
                        register_spread_pat(spread_node, buf);
                    }

                    self.add_stack_members_in_pat_to_buf(field, buf);
                }
            }
            ast::Pat::Or(or_pat) => match or_pat.variants.get(0) {
                // @@Invariant: Here we assume that each branch of the or pattern has the same
                // members This should have already been checked at pre-tc semantics.
                Some(pat) => self.add_stack_members_in_pat_to_buf(pat.ast_ref(), buf),
                None => panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "Found empty or pattern"
                ),
            },
            ast::Pat::If(if_pat) => self.add_stack_members_in_pat_to_buf(if_pat.pat.ast_ref(), buf),
            ast::Pat::Wild(_) => buf.push((
                node.id(),
                StackMemberData {
                    name: self.new_fresh_symbol(),
                    is_mutable: false,
                    ty: self.new_ty_hole(),
                    value: None,
                },
            )),
            ast::Pat::Access(_) | ast::Pat::Lit(_) | ast::Pat::Range(_) => {}
        }
    }

    /// Add a pattern node to the given `stack_id` (which is
    /// "current").
    ///
    /// This adds the pattern binds as a set of stack members. It adds a set of
    /// tuples `(AstNodeId, StackMemberData)`, one for each binding, where
    /// the `AstNodeId` is the `AstNodeId` of the binding pattern node.
    pub(super) fn add_pat_node_binds_to_stack(
        &self,
        node: AstNodeRef<ast::Pat>,
        stack_id: StackId,
        declaration_name: Option<Symbol>,
        rhs: Option<&ast::AstNode<ast::Expr>>,
    ) {
        self.def_state().stack_members.modify_fast(stack_id, |members| {
            let members = match members {
                Some(members) => members,
                None => {
                    panic!("Got empty members for stack {stack_id:?}");
                }
            };

            // Add each stack member to the stack_members vector
            let mut found_members = smallvec![];
            match (declaration_name, node.body()) {
                (Some(declaration_name), ast::Pat::Binding(binding_pat))
                    if self
                        .stores()
                        .symbol()
                        .map_fast(declaration_name, |sym| Some(binding_pat.name.ident == sym.name?))
                        .contains(&true) =>
                {
                    found_members.push((
                        node.id(),
                        StackMemberData {
                            name: declaration_name,
                            is_mutable: binding_pat.mutability.as_ref().map(|m| *m.body())
                                == Some(ast::Mutability::Mutable),
                            ty: self.new_ty_hole(),
                            value: rhs.as_ref().map(|_| self.new_term_hole()),
                        },
                    ))
                }
                _ => self.add_stack_members_in_pat_to_buf(node, &mut found_members),
            }
            for (node_id, stack_member) in found_members {
                members.push((node_id, stack_member));
            }
        });
    }

    /// Add the location of the given node to the given `DefId`, as appropriate
    /// depending on the variant.
    pub(super) fn add_node_location_to_def<U>(
        &self,
        def_id: DefId,
        originating_node: AstNodeRef<U>,
    ) {
        self.stores()
            .location()
            .add_location_to_target(def_id, self.node_location(originating_node));
    }
}
