//! Utilities for keeping track of definitions during the discovery pass.
use std::{fmt::Display, option::Option};

use hash_ast::ast::{self, AstNode, AstNodeId, AstNodeRef, OwnsAstNode};
use hash_reporting::macros::panic_on_span;
use hash_source::{identifier::Identifier, ModuleId, SourceMapUtils};
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    DefaultPartialStore, PartialStore, SequenceStoreKey, StoreKey,
};
use hash_tir::{
    context::ContextMember,
    scopes::StackId,
    tir::{
        CtorDef, CtorDefData, CtorDefId, DataDefCtors, DataDefId, FnDefId, HasAstNodeId, ModDef,
        ModDefId, ModKind, ModMember, ModMemberId, ModMemberValue, Node, NodeId, NodeOrigin,
        NodesId, SymbolId, TyId,
    },
};
use hash_utils::{
    derive_more::From,
    smallvec::{smallvec, SmallVec},
    state::LightState,
};

use super::DiscoveryPass;
use crate::env::SemanticEnv;

/// The ID of some definition.
///
/// This is used to refer to a definition in a generic way, without knowing
/// what kind of definition it is.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
pub enum DefId {
    Mod(ModDefId),
    Data(DataDefId),
    Fn(FnDefId),
    Stack(StackId),
}

impl HasAstNodeId for DefId {
    fn node_id(&self) -> Option<hash_ast::ast::AstNodeId> {
        match *self {
            DefId::Mod(id) => id.node_id(),
            DefId::Data(id) => id.node_id(),
            DefId::Fn(id) => id.node_id(),
            DefId::Stack(id) => id.node_id(),
        }
    }
}

impl Display for DefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DefId::Mod(mod_id) => write!(f, "{}", mod_id),
            DefId::Data(data_id) => write!(f, "{}", data_id),
            DefId::Fn(fn_id) => write!(f, "{}", fn_id),
            DefId::Stack(stack_id) => write!(f, "{}", stack_id),
        }
    }
}

/// An item that is discovered: either a definition or a function type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, From)]
pub(super) enum ItemId {
    Def(DefId),
    Ty(TyId),
}

/// Either a stack member or a mod member.
///
/// This is used for traversing blocks that might also
/// contain local definitions.
#[derive(Debug, Copy, Clone, From)]
enum StackMemberOrModMember {
    StackMember(ContextMember),
    ModMember(ModMember),
}

/// Contains information about seen definitions, members of definitions, as well
/// as the "current" definition we are in. Also holds a name hint so that
/// declarations like `X := mod {}` can be given the name `X`.
#[derive(Debug, Default)]
pub(super) struct DefDiscoveryState {
    /// The current definition we are in.
    currently_in: LightState<Option<ItemId>>,
    /// The mod member we have seen, indexed by the mod ID.
    mod_members: DefaultPartialStore<ModDefId, Vec<(AstNodeId, ModMember)>>,
    /// The data ctor we have seen, indexed by the data definition ID.
    data_ctors: DefaultPartialStore<DataDefId, Vec<(AstNodeId, CtorDefData)>>,
    /// The stack members we have seen, indexed by the stack ID.
    stack_members: DefaultPartialStore<StackId, Vec<(AstNodeId, StackMemberOrModMember)>>,
}

impl DefDiscoveryState {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'env, E: SemanticEnv + 'env> DiscoveryPass<'env, E> {
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
        let node_id = originating_node.id();

        // Add the definition to the member context.
        match def_id {
            DefId::Mod(id) => {
                self.def_state().mod_members.insert(id, vec![]);
                self.ast_info.mod_defs().insert(node_id, id);
            }
            DefId::Data(id) => {
                self.def_state().data_ctors.insert(id, vec![]);
                self.ast_info.data_defs().insert(node_id, id);
            }
            DefId::Stack(id) => {
                self.def_state().stack_members.insert(id, vec![]);
            }
            DefId::Fn(id) => {
                self.ast_info.fn_defs().insert(node_id, id);
            }
        }

        let result = self.enter_item(originating_node, ItemId::Def(def_id), f);

        // Add the found members to the definition.
        self.add_found_members_to_def(def_id);

        result
    }

    /// Get the "current" definition, or `None` if there is none.
    pub(super) fn get_current_item(&self) -> Option<ItemId> {
        self.def_state().currently_in.get()
    }

    /// Add the given definition to the AST info of the given node.
    pub(super) fn add_def_to_ast_info<U>(&self, item_id: ItemId, node: AstNodeRef<U>) {
        match item_id {
            ItemId::Def(def_id) => match def_id {
                DefId::Mod(id) => self.ast_info.mod_defs().insert(node.id(), id),
                DefId::Data(id) => self.ast_info.data_defs().insert(node.id(), id),
                DefId::Fn(id) => self.ast_info.fn_defs().insert(node.id(), id),
                DefId::Stack(id) => self.ast_info.stacks().insert(node.id(), id),
            },
            ItemId::Ty(id) => self.ast_info.tys().insert(node.id(), id),
        };
    }

    /// Create or get an existing module definition by `[SourceId]`.
    pub fn create_or_get_module_mod_def(&self, module_id: ModuleId) -> ModDefId {
        let source_node_id = self.node_map().get_module(module_id).node_ref().id();
        match self.ast_info.mod_defs().get_data_by_node(source_node_id) {
            Some(existing) => existing,
            None => {
                // Create a new module definition.
                let source_id = module_id.into();
                let module_name: Identifier =
                    SourceMapUtils::map(source_id, |source| source.name().into());

                // @@MissingOrigin
                Node::create_at(
                    ModDef {
                        name: SymbolId::from_name(module_name, NodeOrigin::Generated),
                        kind: ModKind::Source(source_id),
                        members: Node::create_at(
                            Node::<ModMember>::empty_seq(),
                            NodeOrigin::Generated,
                        ),
                    },
                    NodeOrigin::Generated,
                )
            }
        }
    }

    /// Add the found members of the given definitions to the definitions
    /// themselves, as well as to the `ast_info` stores.
    ///
    /// We store a tuple `(AstNodeId, MemberData)` for each member we find in
    /// the scope discovery. Therefore, we first create a `Member` from the
    /// `MemberData` and then using its `MemberId` and `AstNodeId` we add it to
    /// `AstInfo` store, appropriately depending on the definition kind,
    pub(super) fn add_found_members_to_def(&self, def_id: impl Into<DefId>) {
        let ast_info = self.ast_info;
        match def_id.into() {
            DefId::Mod(mod_def_id) => {
                self.def_state().mod_members.modify_fast(mod_def_id, |members| {
                    if let Some(members) = members {
                        let members = std::mem::take(members);

                        // Set module members.
                        let mod_members = Node::create_at(
                            Node::<ModMember>::seq(members.iter().map(|(node, data)| {
                                Node::at(
                                    ModMember { name: data.name, value: data.value },
                                    NodeOrigin::Given(*node),
                                )
                            })),
                            // Origin should be already set in the visitor:
                            mod_def_id.value().members.origin(),
                        );
                        mod_def_id.borrow_mut().members = mod_members;

                        // Set node for each member.
                        for ((node_id, _), mod_member_index) in
                            members.iter().zip(mod_members.to_index_range())
                        {
                            ast_info.mod_members().insert(
                                *node_id,
                                ModMemberId(mod_members.elements(), mod_member_index),
                            );
                        }
                    }
                })
            }
            DefId::Data(data_def_id) => {
                self.def_state().data_ctors.modify_fast(data_def_id, |members| {
                    if let Some(members) = members {
                        let members = std::mem::take(members);

                        let ctors_origin = match data_def_id.value().ctors {
                            DataDefCtors::Defined(d) => d.origin(),
                            DataDefCtors::Primitive(_) => unreachable!(
                                "Primitive data definition not allowed during discovery: {}",
                                data_def_id
                            ),
                        };

                        // Set data constructors.
                        let ctors = CtorDef::seq_from_data(
                            data_def_id,
                            members
                                .iter()
                                .map(|(node, data)| Node::at(*data, NodeOrigin::Given(*node))),
                            ctors_origin,
                        );
                        data_def_id.borrow_mut().ctors = DataDefCtors::Defined(ctors);

                        // Set node for each data constructor.
                        for ((node_id, _), data_ctor_index) in
                            members.iter().zip(ctors.to_index_range())
                        {
                            ast_info
                                .ctor_defs()
                                .insert(*node_id, CtorDefId(ctors.elements(), data_ctor_index));
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

                        let (mut stack_members, mut mod_members) = (vec![], vec![]);
                        for (id, data) in members {
                            match data {
                                StackMemberOrModMember::StackMember(stack_member_data) => {
                                    stack_members.push((id, stack_member_data));
                                }
                                StackMemberOrModMember::ModMember(mod_member_data) => {
                                    mod_members.push((id, mod_member_data));
                                }
                            }
                        }

                        // Set stack members.
                        stack_id.borrow_mut().members =
                            stack_members.iter().map(|(_, data)| *data).collect();

                        // Set node for each stack member.
                        for (node_id, decl) in stack_members.iter() {
                            ast_info.stack_members().insert(*node_id, *decl);
                        }

                        // If we got local mod members, create a new mod def and
                        // add it to the stack definition.
                        if !mod_members.is_empty() {
                            let stack_origin = stack_id.origin();
                            let local_mod_def_id = Node::create_at(
                                ModDef {
                                    kind: ModKind::ModBlock,
                                    name: SymbolId::from_name(
                                        format!("stack_mod_{}", stack_id.to_index()),
                                        stack_origin,
                                    ),
                                    members: Node::create_at(
                                        Node::<ModMember>::empty_seq(),
                                        stack_origin,
                                    ),
                                },
                                stack_origin,
                            );
                            stack_id.borrow_mut().local_mod_def = Some(local_mod_def_id);
                            self.def_state().mod_members.insert(local_mod_def_id, mod_members);

                            // Add to AST info and locations, forwarded from the stack.
                            ast_info.mod_defs().insert(
                                ast_info.stacks().get_node_by_data(stack_id).unwrap(),
                                local_mod_def_id,
                            );

                            // Add the members to the local mod def.
                            self.add_found_members_to_def(local_mod_def_id)
                        }
                    }
                })
            }
        }
    }

    /// Whether the given stack declaration node can be turned into a member of
    /// a module.
    pub(super) fn stack_declaration_is_mod_member(
        &self,
        node: AstNodeRef<ast::Declaration>,
    ) -> bool {
        let def_node_id = match node.value.body() {
            // If the declaration is a block, we need to get the
            // right node to look up the members
            ast::Expr::Block(block) => block.data.id(),
            _ => node.value.id(),
        };

        // Function definitions are not considered module members in stack
        // scope, they are considered closures instead.
        // @@Improvement: We could consider them module members if they do not
        // capture any variables.

        // Data definition or nested module in a module
        self.ast_info.data_defs().get_data_by_node(def_node_id).is_some()
            || self.ast_info.mod_defs().get_data_by_node(def_node_id).is_some()
    }

    /// Get the module member data for the given definition node id, if it
    /// exists
    pub fn get_mod_member_data_from_def_node_id(
        &self,
        name: SymbolId,
        def_node_id: AstNodeId,
    ) -> Option<ModMember> {
        if let Some(fn_def_id) = self.ast_info.fn_defs().get_data_by_node(def_node_id) {
            // Function definition in a module
            Some(ModMember { name, value: ModMemberValue::Fn(fn_def_id) })
        } else if let Some(data_def_id) = self.ast_info.data_defs().get_data_by_node(def_node_id) {
            // Data definition in a module
            Some(ModMember { name, value: ModMemberValue::Data(data_def_id) })
        } else {
            // Nested module definition
            self.ast_info.mod_defs().get_data_by_node(def_node_id).map(|nested_mod_def_id| {
                ModMember { name, value: ModMemberValue::Mod(nested_mod_def_id) }
            })

            // If the above `get_data_by_node` returns `None`, do
            // nothing because there might have been a recoverable
            // error in a declaration which could have led to no
            // `AstInfo` being recorded.
        }
    }

    /// Create `ModMember` from a declaration node.
    pub(super) fn make_mod_member_data_from_declaration_node(
        &self,
        name: SymbolId,
        node: AstNodeRef<ast::Declaration>,
    ) -> Option<ModMember> {
        // The `def_node_id` is the `AstNodeId` of the actual definition value that
        // this declaration is pointing to. For example, in `Y := mod {...}`, the `mod`
        // node's ID (which is a block) would be `def_node_id`.
        let def_node_id = match node.value.body() {
            // If the declaration is a block, we need to get the
            // right node to look up the members
            ast::Expr::Block(block) => block.data.id(),
            _ => node.value.id(),
        };

        match node.value.body() {
            // Import
            ast::Expr::Import(import_expr) => {
                let source_id = import_expr.data.source;
                let imported_mod_def_id = self.create_or_get_module_mod_def(source_id.into());
                Some(ModMember { name, value: ModMemberValue::Mod(imported_mod_def_id) })
            }
            // Directive, recurse
            ast::Expr::Macro(inner) => {
                self.get_mod_member_data_from_def_node_id(name, inner.subject.id())
            }
            // Get the `ModMember` from the `def_node_id` of the declaration.
            _ => self.get_mod_member_data_from_def_node_id(name, def_node_id),
        }
    }

    /// Add a declaration node `a := b` to the given `mod_def_id` (which is
    /// "current").
    ///
    /// This will add the appropriate `MemberData` to the `mod_members` local
    /// score. In other words, a tuple `(AstNodeId, ModMember)`. The
    /// `ModMember` is found by looking at the `ast_info` of the value of
    /// the declaration, which denotes if the value is a resolved
    /// module/function/data definition etc. If the value is not resolved, then
    /// it is not a valid module member.
    pub(super) fn add_declaration_node_to_mod_def(
        &self,
        name: SymbolId,
        node: AstNodeRef<ast::Declaration>,
        mod_def_id: ModDefId,
    ) {
        if let Some(mod_member_data) = self.make_mod_member_data_from_declaration_node(name, node) {
            self.def_state().mod_members.modify_fast(mod_def_id, |members| {
                let members = match members {
                    Some(members) => members,
                    None => {
                        panic!("Got empty members for mod def {mod_def_id:?}");
                    }
                };
                members.push((node.id(), mod_member_data));
            });
        }
    }

    /// Add a mod member to the given `stack_id` as a local definition.
    pub(super) fn add_mod_member_to_stack(
        &self,
        stack_id: StackId,
        mod_member_node_id: AstNodeId,
        mod_member: ModMember,
    ) {
        self.def_state().stack_members.modify_fast(stack_id, |members| {
            let members = match members {
                Some(members) => members,
                None => {
                    panic!("Got empty locals for stack {stack_id:?}");
                }
            };
            members.push((mod_member_node_id, mod_member.into()));
        });
    }

    /// Create and add `StackMemberData` values to the given `buf`, from the
    /// given pattern `node`.
    ///
    /// This recursively adds all the bindings of the pattern as stack members.
    /// It leaves types as holes and values as `None`, because they will be
    /// resolved at a later stage.
    pub(super) fn add_stack_members_in_pat_to_buf(
        node: AstNodeRef<ast::Pat>,
        buf: &mut SmallVec<[(AstNodeId, ContextMember); 3]>,
    ) {
        let register_spread_pat =
            |spread: &AstNode<ast::SpreadPat>,
             buf: &mut SmallVec<[(AstNodeId, ContextMember); 3]>| {
                if let Some(name) = &spread.name {
                    buf.push((
                        name.id(),
                        ContextMember {
                            name: SymbolId::from_name(name.ident, NodeOrigin::Given(name.id())),
                            ty: None,
                            value: None,
                        },
                    ))
                }
            };

        match node.body() {
            ast::Pat::Binding(binding) => {
                buf.push((
                    node.id(),
                    ContextMember {
                        name: SymbolId::from_name(
                            binding.name.ident,
                            NodeOrigin::Given(binding.name.id()),
                        ),
                        ty: None,
                        value: None,
                    },
                ));
            }
            ast::Pat::Module(_) => {
                // This should have been handled pre-tc semantics
                panic_on_span!(node.span(), "Found module pattern in stack definition")
            }
            ast::Pat::Tuple(ast::TuplePat { fields, spread }) => {
                if let Some(spread_node) = &spread {
                    register_spread_pat(spread_node, buf);
                }
                for field in fields.ast_ref_iter() {
                    Self::add_stack_members_in_pat_to_buf(field.pat.ast_ref(), buf);
                }
            }
            ast::Pat::Constructor(ast::ConstructorPat { fields, spread, .. }) => {
                if let Some(spread_node) = &spread {
                    register_spread_pat(spread_node, buf);
                }
                for field in fields.ast_ref_iter() {
                    Self::add_stack_members_in_pat_to_buf(field.pat.ast_ref(), buf);
                }
            }
            ast::Pat::Macro(ast::PatMacroInvocation { subject, .. }) => {
                Self::add_stack_members_in_pat_to_buf(subject.ast_ref(), buf)
            }
            ast::Pat::Array(ast::ArrayPat { fields, spread }) => {
                if let Some(spread_node) = &spread {
                    register_spread_pat(spread_node, buf);
                }

                for field in fields.ast_ref_iter() {
                    Self::add_stack_members_in_pat_to_buf(field, buf);
                }
            }
            ast::Pat::Or(or_pat) => match or_pat.variants.get(0) {
                // @@Invariant: Here we assume that each branch of the or pattern has the same
                // members This should have already been checked at pre-tc semantics.
                Some(pat) => Self::add_stack_members_in_pat_to_buf(pat.ast_ref(), buf),
                None => panic_on_span!(node.span(), "Found empty or pattern"),
            },
            ast::Pat::If(if_pat) => {
                Self::add_stack_members_in_pat_to_buf(if_pat.pat.ast_ref(), buf)
            }
            ast::Pat::Wild(_) => buf.push((
                node.id(),
                ContextMember {
                    name: SymbolId::fresh(NodeOrigin::Given(node.id())),
                    // is_mutable: false,
                    ty: None,
                    value: None,
                },
            )),
            ast::Pat::Access(_)
            | ast::Pat::Lit(_)
            | ast::Pat::Range(_)
            | ast::Pat::TokenMacro(_) => {}
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
        declaration_name: Option<SymbolId>,
        _rhs: Option<&ast::AstNode<ast::Expr>>,
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
                    if declaration_name.borrow().name == Some(binding_pat.name.ident) =>
                {
                    found_members.push((
                        node.id(),
                        ContextMember { name: declaration_name, ty: None, value: None },
                    ))
                }
                _ => Self::add_stack_members_in_pat_to_buf(node, &mut found_members),
            }
            for (node_id, stack_member) in found_members {
                members.push((node_id, stack_member.into()));
            }
        });
    }
}
