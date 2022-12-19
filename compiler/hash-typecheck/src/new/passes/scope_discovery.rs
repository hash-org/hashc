/// The first pass of the typechecker, which discovers the scopes of all
/// declarations in the source.
///
/// This pass finds the following items:
/// - Modules/module blocks
/// - Function definitions in modules
/// - Data definitions in modules, including struct, enum
/// - Stack scopes, and their member names and mutabilities
use std::{
    cell::Cell,
    iter::{empty, once},
};

use derive_more::From;
use hash_ast::{
    ast::{self, AstNodeId, AstNodeRef},
    ast_visitor_default_impl,
    visitor::{walk, AstVisitor},
};
use hash_reporting::macros::panic_on_span;
use hash_source::identifier::Identifier;
use hash_types::new::{
    data::{CtorDefData, DataDefId},
    defs::{DefParamGroupData, DefParamsId},
    environment::env::AccessToEnv,
    fns::{FnBody, FnDefData, FnDefId, FnTy},
    mods::{ModDefData, ModDefId, ModKind, ModMemberData, ModMemberValue},
    params::{ParamData, ParamsId},
    scopes::{StackId, StackMemberData},
    symbols::Symbol,
};
use hash_utils::store::{DefaultPartialStore, PartialStore, SequenceStoreKey, Store};
use itertools::Itertools;
use smallvec::{smallvec, SmallVec};

use super::{ast_ops::AstOps, ast_pass::AstPass};
use crate::{
    impl_access_to_tc_env,
    new::{
        diagnostics::error::TcError,
        environment::tc_env::{AccessToTcEnv, TcEnv},
        ops::{common::CommonOps, AccessToOps},
    },
};

/// The ID of some definition.
///
/// These definitions are the ones handled by this pass.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
enum DefId {
    Mod(ModDefId),
    Data(DataDefId),
    Fn(FnDefId),
    Stack(StackId),
}

/// Contains information about seen definitions, members of definitions, as well
/// as the "current" definition we are in. Also holds a name hint so that
/// declarations like `X := mod {}` can be given the name `X`.
pub struct ScopeDiscoveryPass<'tc> {
    tc_env: &'tc TcEnv<'tc>,
    /// The name hint for the current definition.
    name_hint: Cell<Option<Symbol>>,
    /// The current definition we are in.
    currently_in: Cell<Option<DefId>>,
    /// The mod member we have seen, indexed by the mod ID.
    mod_members: DefaultPartialStore<ModDefId, Vec<(AstNodeId, ModMemberData)>>,
    /// The data ctor we have seen, indexed by the data definition ID.
    data_ctors: DefaultPartialStore<DataDefId, Vec<(AstNodeId, CtorDefData)>>,
    /// The stack members we have seen, indexed by the stack ID.
    stack_members: DefaultPartialStore<StackId, Vec<(AstNodeId, StackMemberData)>>,
}

impl<'tc> AstPass for ScopeDiscoveryPass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        self.visit_body_block(node)
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        self.visit_module(node)
    }
}

impl<'tc> ScopeDiscoveryPass<'tc> {
    pub fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        Self {
            tc_env,
            name_hint: Cell::new(None),
            currently_in: Cell::new(None),
            data_ctors: DefaultPartialStore::new(),
            mod_members: DefaultPartialStore::new(),
            stack_members: DefaultPartialStore::new(),
        }
    }

    /// Run the given closure with the given name hint, resetting it at the end.
    fn with_name_hint<T>(&self, name_hint: Option<Symbol>, mut f: impl FnMut() -> T) -> T {
        let prev_hint = self.name_hint.get();
        self.name_hint.set(name_hint);
        let result = f();
        self.name_hint.set(prev_hint);
        result
    }

    /// Create a new symbol from the given optional AST node containing a name.
    ///
    /// If the AST node is `None`, a fresh symbol is created.
    fn create_symbol_from_ast_name(&self, ast_name: &Option<ast::AstNode<ast::Name>>) -> Symbol {
        match ast_name {
            Some(ast_name) => self.new_symbol(ast_name.ident),
            None => self.new_fresh_symbol(),
        }
    }

    /// Create definition params from the iterator of parameter groups.
    ///
    /// The iterator elements are `(is_implicit, params)`.
    fn create_hole_def_params<'a>(
        &self,
        groups: impl Iterator<Item = (bool, &'a ast::AstNodes<ast::Param>)> + ExactSizeIterator,
    ) -> DefParamsId {
        let params = groups
            .filter(|group| !group.1.is_empty())
            .map(|group| {
                let (implicit, params) = group;
                DefParamGroupData { params: self.create_hole_params(params), implicit }
            })
            .collect_vec();
        self.param_ops().create_def_params(params.into_iter())
    }

    /// Create a parameter list from the given AST parameter list, where the
    /// type of each parameter is a hole.
    fn create_hole_params(&self, params: &ast::AstNodes<ast::Param>) -> ParamsId {
        self.param_ops().create_hole_params(
            params.iter().map(|param| self.create_symbol_from_ast_name(&param.name)),
        )
    }

    /// Create a parameter data list from the given AST parameter list, where
    /// the type and default value of each parameter is a hole.
    fn create_param_data_from_ast_params<'a>(
        &self,
        params: impl Iterator<Item = &'a ast::AstNode<ast::Param>> + ExactSizeIterator,
    ) -> Vec<ParamData> {
        params
            .map(|param| {
                let name = self.create_symbol_from_ast_name(&param.name);
                let ty = self.new_ty_hole();
                let default_value = param.default.as_ref().map(|_| self.new_term_hole());
                ParamData { name, ty, default_value }
            })
            .collect_vec()
    }

    /// Take the currently set name hint, or create a new internal name.
    fn take_name_hint_or_create_internal_name(&self) -> Symbol {
        self.name_hint.take().unwrap_or_else(|| self.new_fresh_symbol())
    }

    /// Run the given closure with the given definition as "current", resetting
    /// it at the end. It does not handle definition members.
    ///
    /// This will add the definition to the originating node in `ast_info`. The
    /// originating node is the node that represents the definition, e.g.
    /// the `mod` node for `X := mod {...}`.
    fn enter_def_without_members<T, U>(
        &self,
        originating_node: AstNodeRef<U>,
        def_id: impl Into<DefId>,
        mut f: impl FnMut() -> T,
    ) -> T {
        let def_id = def_id.into();

        // Add the definition to the originating node.
        self.add_def_to_ast_info(def_id, originating_node);

        let prev_def = self.currently_in.get();
        self.currently_in.set(Some(def_id));
        let result = f();
        self.currently_in.set(prev_def);

        result
    }

    /// Run the given closure with the given definition as "current", resetting
    /// it at the end.
    ///
    /// This will add found sub-definitions/members to the entered definition
    /// after exiting, if applicable. It will also add the definition to the
    /// originating node in `ast_info`. The originating node is the node that
    /// represents the definition, e.g. the `mod` node for `X := mod {...}`.
    fn enter_def<T, U>(
        &self,
        originating_node: AstNodeRef<U>,
        def_id: impl Into<DefId>,
        f: impl FnMut() -> T,
    ) -> T {
        let def_id = def_id.into();

        // Add the definition to the member context.
        match def_id {
            DefId::Mod(id) => {
                self.mod_members.insert(id, vec![]);
            }
            DefId::Data(id) => {
                self.data_ctors.insert(id, vec![]);
            }
            DefId::Stack(id) => {
                self.stack_members.insert(id, vec![]);
            }
            DefId::Fn(_) => {}
        }

        let result = self.enter_def_without_members(originating_node, def_id, f);

        // Add the found members to the definition.
        self.add_found_members_to_def(def_id);

        result
    }

    /// Get the "current" definition, or panic if there is none.
    fn get_current_def(&self) -> DefId {
        self.currently_in.get().unwrap_or_else(|| panic!("Tried to get def but none was set"))
    }

    /// Add the given definition to the AST info of the given node.
    fn add_def_to_ast_info<U>(&self, def_id: DefId, node: AstNodeRef<U>) {
        let ast_info = self.ast_info();
        match def_id {
            DefId::Mod(id) => ast_info.mod_defs.insert(node.id(), id),
            DefId::Data(id) => ast_info.data_defs.insert(node.id(), id),
            DefId::Fn(id) => ast_info.fn_defs.insert(node.id(), id),
            DefId::Stack(id) => ast_info.stacks.insert(node.id(), id),
        };
    }

    /// Add the found members of the given definitions to the definitions
    /// themselves, as well as to the `ast_info` stores.
    ///
    /// We store a tuple `(AstNodeId, MemberData)` for each member we find in
    /// the scope discovery. Therefore, we first create a `Member` from the
    /// `MemberData` and then using its `MemberId` and `AstNodeId` we add it to
    /// `AstInfo` store, appropriately depending on the definition kind,
    fn add_found_members_to_def(&self, def_id: impl Into<DefId>) {
        let ast_info = self.ast_info();
        match def_id.into() {
            DefId::Mod(mod_def_id) => self.mod_members.modify_fast(mod_def_id, |members| {
                if let Some(members) = members {
                    let members = std::mem::take(members);
                    let mod_ops = self.mod_ops();

                    // Set module members.
                    let mod_members = mod_ops.set_mod_def_members(
                        mod_def_id,
                        mod_ops.create_mod_members(members.iter().map(|(_, data)| data).cloned()),
                    );

                    // Set node for each member.
                    for ((node_id, _), mod_member_index) in
                        members.iter().zip(mod_members.to_index_range())
                    {
                        ast_info.mod_members.insert(*node_id, (mod_members, mod_member_index));
                    }
                }
            }),
            DefId::Data(data_def_id) => self.data_ctors.modify_fast(data_def_id, |members| {
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
                        ast_info.ctor_defs.insert(*node_id, (data_members, data_ctor_index));
                    }
                }
            }),
            DefId::Fn(_) => {
                // Nothing to do here, functions don't have members.
            }
            DefId::Stack(stack_id) => self.stack_members.modify_fast(stack_id, |members| {
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
                        ast_info.stack_members.insert(*node_id, (stack_id, member_index));
                    }
                }
            }),
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
    fn add_declaration_node_to_mod_def(
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
        self.mod_members.modify_fast(mod_def_id, |members| {
            let members = match members {
                Some(members) => members,
                None => {
                    panic!("Got empty members for mod def {mod_def_id:?}");
                }
            };

            if let Some(fn_def_id) = ast_info.fn_defs.get_data_by_node(def_node_id) {
                // Function definition in a module
                self.stores().fn_def().map_fast(fn_def_id, |fn_def| {
                    members.push((
                        node.id(),
                        ModMemberData { name: fn_def.name, value: ModMemberValue::Fn(fn_def_id) },
                    ));
                })
            } else if let Some(data_def_id) = ast_info.data_defs.get_data_by_node(def_node_id) {
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
            } else if let Some(nested_mod_def_id) = ast_info.mod_defs.get_data_by_node(def_node_id)
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
            } else if ast_info.stacks.get_data_by_node(def_node_id).is_some() {
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
    fn add_stack_members_in_pat_to_buf(
        &self,
        node: AstNodeRef<ast::Pat>,
        buf: &mut SmallVec<[(AstNodeId, StackMemberData); 3]>,
    ) {
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
            ast::Pat::Tuple(tuple_pat) => {
                for entry in tuple_pat.fields.ast_ref_iter() {
                    self.add_stack_members_in_pat_to_buf(entry.pat.ast_ref(), buf);
                }
            }
            ast::Pat::Constructor(constructor_pat) => {
                for field in constructor_pat.fields.ast_ref_iter() {
                    self.add_stack_members_in_pat_to_buf(field.pat.ast_ref(), buf);
                }
            }
            ast::Pat::List(list_pat) => {
                for pat in list_pat.fields.ast_ref_iter() {
                    self.add_stack_members_in_pat_to_buf(pat, buf);
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
            ast::Pat::Spread(spread_pat) => {
                if let Some(name) = spread_pat.name.as_ref() {
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
            }
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

    /// Add a declaration node `a := b` to the given `stack_id` (which is
    /// "current").
    ///
    /// This adds the declaration as a set of stack members, taking into account
    /// all of the pattern bindings. It adds a set of tuples `(AstNodeId,
    /// StackMemberData)`, one for each binding, where the `AstNodeId` is
    /// the `AstNodeId` of the binding pattern node.
    fn add_declaration_node_to_stack(&self, node: AstNodeRef<ast::Declaration>, stack_id: StackId) {
        self.stack_members.modify_fast(stack_id, |members| {
            let members = match members {
                Some(members) => members,
                None => {
                    panic!("Got empty members for stack {stack_id:?}");
                }
            };

            // Add each stack member to the stack_members vector
            let mut found_members = smallvec![];
            self.add_stack_members_in_pat_to_buf(node.pat.ast_ref(), &mut found_members);
            for (node_id, stack_member) in found_members {
                members.push((node_id, stack_member));
            }
        });
    }
}

impl_access_to_tc_env!(ScopeDiscoveryPass<'tc>);

impl<'tc> ast::AstVisitor for ScopeDiscoveryPass<'tc> {
    type Error = TcError;
    ast_visitor_default_impl!(
        hiding: Declaration,
        Module,
        ModDef,
        TraitDef,
        StructDef,
        EnumDef,
        FnDef,
        TyFnDef,
        BodyBlock,
        MergeDeclaration
    );

    type DeclarationRet = ();
    fn visit_declaration(
        &self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let walk_with_name_hint = || {
            let name = match node.pat.body() {
                ast::Pat::Binding(binding) => Some(self.new_symbol(binding.name.ident)),
                // If the pattern is not a binding, we don't know the name of the declaration
                _ => None,
            };
            // Walk the node
            self.with_name_hint(name, || walk::walk_declaration(self, node))
        };

        // Add the declaration to the current definition as appropriate
        match self.get_current_def() {
            DefId::Mod(mod_def_id) => {
                walk_with_name_hint()?;
                self.add_declaration_node_to_mod_def(node, mod_def_id)
            }
            DefId::Data(_) => {
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "found declaration in data definition scope, which should have been handled earlier"
                )
            }
            DefId::Stack(stack_id) => {
                walk_with_name_hint()?;
                self.add_declaration_node_to_stack(node, stack_id)
            }
            DefId::Fn(_) => {
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "found declaration in function scope, which should instead be in its stack scope"
                )
            }
        };

        Ok(())
    }

    type ModuleRet = ();
    fn visit_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let source_id = self.current_source_info().source_id;
        let module_name: Identifier = self.source_map().source_name(source_id).into();

        // Create a module definition, with empty members for now.
        // @@Future: context
        let mod_def_id = self.mod_ops().create_mod_def(ModDefData {
            name: self.new_symbol(module_name),
            params: self.create_hole_def_params(empty()),
            kind: ModKind::Source(source_id),
            members: self.mod_ops().create_empty_mod_members(),
            self_ty_name: None,
        });

        // Traverse the module
        self.enter_def(node, mod_def_id, || walk::walk_module(self, node))?;

        // Eventually remove @@Temporary
        println!("Module: {}", self.env().with(mod_def_id));

        Ok(())
    }

    type ModDefRet = ();
    fn visit_mod_def(
        &self,
        node: ast::AstNodeRef<ast::ModDef>,
    ) -> Result<Self::ModDefRet, Self::Error> {
        // Get the mod block name from the name hint.
        let mod_block_name = self.take_name_hint_or_create_internal_name();

        // Create a mod block definition, with empty members for now.
        let mod_def_id = self.mod_ops().create_mod_def(ModDefData {
            name: mod_block_name,
            params: self.create_hole_def_params(once((true, &node.ty_params))),
            kind: ModKind::ModBlock,
            members: self.mod_ops().create_empty_mod_members(),
            self_ty_name: None,
        });

        // Traverse the mod block
        self.enter_def(node, mod_def_id, || walk::walk_mod_def(self, node))?;

        Ok(())
    }

    type StructDefRet = ();
    fn visit_struct_def(
        &self,
        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let struct_name = self.take_name_hint_or_create_internal_name();

        // Create a data definition for the struct
        let struct_def_id = self.data_ops().create_struct_def(
            struct_name,
            self.create_hole_def_params(once((true, &node.ty_params))),
            self.create_param_data_from_ast_params(node.fields.iter()).into_iter(),
        );

        // Traverse the struct; note that the fields have already been created, they
        // will not be created below like with mods.
        self.enter_def_without_members(node, struct_def_id, || walk::walk_struct_def(self, node))?;

        Ok(())
    }

    type EnumDefRet = ();
    fn visit_enum_def(
        &self,
        node: ast::AstNodeRef<ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let enum_name = self.take_name_hint_or_create_internal_name();

        // Create a data definition for the enum
        let enum_def_id = self.data_ops().create_enum_def(
            enum_name,
            self.create_hole_def_params(once((true, &node.ty_params))),
            node.entries.iter().map(|variant| {
                (
                    self.new_symbol(variant.name.ident),
                    self.create_param_data_from_ast_params(variant.fields.iter()).into_iter(),
                )
            }),
        );

        // Traverse the enum; the variants have already been created.
        self.enter_def_without_members(node, enum_def_id, || walk::walk_enum_def(self, node))?;

        Ok(())
    }

    type FnDefRet = ();
    fn visit_fn_def(&self, node: AstNodeRef<ast::FnDef>) -> Result<Self::FnDefRet, Self::Error> {
        // Get the function name from the name hint.
        let fn_def_name = self.take_name_hint_or_create_internal_name();

        // Create a function definition
        let fn_def_id = self.fn_ops().create_fn_def(FnDefData {
            name: fn_def_name,
            body: FnBody::Defined(self.new_term_hole()),
            ty: FnTy {
                implicit: false,
                is_unsafe: false,
                params: self.create_hole_params(&node.params),
                pure: false,
                return_type: self.new_ty_hole(),
            },
        });

        // Traverse the function body
        self.enter_def(node, fn_def_id, || walk::walk_fn_def(self, node))?;

        Ok(())
    }

    type TyFnDefRet = ();
    fn visit_ty_fn_def(
        &self,
        node: AstNodeRef<ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        // Type functions are interpreted as functions that are implicit.

        // Get the function name from the name hint.
        let fn_def_name = self.take_name_hint_or_create_internal_name();

        // Create a function definition
        let fn_def_id = self.fn_ops().create_fn_def(FnDefData {
            name: fn_def_name,
            body: FnBody::Defined(self.new_term_hole()),
            ty: FnTy {
                implicit: true,
                is_unsafe: false,
                params: self.create_hole_params(&node.params),
                pure: true,
                return_type: self.new_ty_hole(),
            },
        });

        // Traverse the function body
        self.enter_def(node, fn_def_id, || walk::walk_ty_fn_def(self, node))?;

        Ok(())
    }

    type BodyBlockRet = ();
    fn visit_body_block(
        &self,
        node: AstNodeRef<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        match self.get_current_def() {
            // If we are in a mod or data block, this isn't a stack scope so we don't do anything.
            DefId::Mod(_) | DefId::Data(_) => {
                walk::walk_body_block(self, node)?;
                Ok(())
            }
            // If we are in a stack scope, this is a nested block, so we add a new stack
            DefId::Stack(_) |
            // If we are in a function, then this is the function's body, so we add a new stack
            DefId::Fn(_) => {
                let stack_id = self.stack_ops().create_stack();
                self.enter_def(node, stack_id, || walk::walk_body_block(self, node))?;
                Ok(())
            }
        }
    }

    type TraitDefRet = ();
    fn visit_trait_def(
        &self,
        node: ast::AstNodeRef<ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        // Traits are not yet supported
        self.diagnostics()
            .add_error(TcError::TraitsNotSupported { trait_location: self.node_location(node) });
        Ok(())
    }

    type MergeDeclarationRet = ();
    fn visit_merge_declaration(
        &self,
        node: AstNodeRef<ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        // Merge declarations are not yet supported
        self.diagnostics()
            .add_error(TcError::TraitsNotSupported { trait_location: self.node_location(node) });
        Ok(())
    }
}
