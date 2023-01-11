//! AST visitor for the discovery pass.
use std::iter::{empty, once};

use hash_ast::{
    ast::{self, AstNodeRef},
    ast_visitor_default_impl,
    visitor::walk,
};
use hash_reporting::macros::panic_on_span;
use hash_source::identifier::Identifier;
use hash_types::new::{
    defs::DefId,
    environment::env::AccessToEnv,
    fns::{FnBody, FnDefData, FnTy},
    mods::{ModDefData, ModKind},
};
use itertools::Itertools;

use super::{super::ast_utils::AstUtils, defs::ItemId, DiscoveryPass};
use crate::new::{
    diagnostics::error::TcError,
    environment::tc_env::AccessToTcEnv,
    ops::{common::CommonOps, AccessToOps},
};

impl<'tc> ast::AstVisitor for DiscoveryPass<'tc> {
    type Error = TcError;
    ast_visitor_default_impl!(
        hiding: Declaration,
        Module,
        ModDef,
        TraitDef,
        StructDef,
        EnumDef,
        FnDef,
        FnTy,
        TyFn,
        TyFnDef,
        BodyBlock,
        MergeDeclaration,
        MatchCase
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
            self.name_hint.enter(name, || walk::walk_declaration(self, node))
        };

        // Add the declaration to the current definition as appropriate
        match self.get_current_item() {
            ItemId::Def(def_id) => match def_id {
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
                    self.add_pat_node_binds_to_stack(node.pat.ast_ref(), stack_id)
                }
                DefId::Fn(_) => {
                    panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "found declaration in function scope, which should instead be in a stack scope"
                )
                }
            },
            ItemId::FnTy(_) => {
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "found declaration in function type scope, which should instead be in a stack scope"
                )
            }
        };

        Ok(())
    }

    type MatchCaseRet = ();
    fn visit_match_case(
        &self,
        node: AstNodeRef<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        match self.get_current_item() {
            ItemId::Def(DefId::Stack(_)) => {
                // A match case creates its own stack scope.
                let stack_id = self.stack_ops().create_stack();
                self.enter_def(node, stack_id, || {
                    self.add_pat_node_binds_to_stack(node.pat.ast_ref(), stack_id);
                    walk::walk_match_case(self, node)
                })?;
                Ok(())
            }
            _ => {
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "found match in non-stack scope"
                )
            }
        }
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
            params: self.create_hole_def_params(
                node.ty_params.first().iter().map(|_| (true, &node.ty_params)),
            ),
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
            self.create_hole_params(&node.fields),
        );

        // Traverse the struct; note that the fields have already been created, they
        // will not be created below like with mods.
        self.enter_item(node, ItemId::Def(struct_def_id.into()), || {
            walk::walk_struct_def(self, node)
        })?;

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
            |_| {
                node.entries
                    .iter()
                    .map(|variant| {
                        (
                            self.new_symbol(variant.name.ident),
                            self.create_hole_params(&variant.fields),
                        )
                    })
                    .collect_vec()
            },
        );

        // Traverse the enum; the variants have already been created.
        self.enter_item(node, ItemId::Def(enum_def_id.into()), || walk::walk_enum_def(self, node))?;

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
                return_ty: self.new_ty_hole(),
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
                return_ty: self.new_ty_hole(),
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
        match self.get_current_item() {
            ItemId::Def(def_id) => match def_id {
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
            },
            ItemId::FnTy(_) => {
                // If we are in a function type, then this is the function's type return, so we
                // add a new stack
                let stack_id = self.stack_ops().create_stack();
                self.enter_def(node, stack_id, || walk::walk_body_block(self, node))?;
                Ok(())
            }
        }
    }

    type TyFnRet = ();
    fn visit_ty_fn(&self, node: AstNodeRef<ast::TyFn>) -> Result<Self::TyFnRet, Self::Error> {
        // This will be filled in during resolution
        let fn_ty_id = self.new_ty(FnTy {
            implicit: true,
            is_unsafe: false,
            params: self.create_hole_params(&node.params),
            pure: true,
            return_ty: self.new_ty_hole(),
        });

        // Traverse the type function body
        self.enter_item(node, fn_ty_id, || walk::walk_ty_fn(self, node))?;

        Ok(())
    }

    type FnTyRet = ();
    fn visit_fn_ty(&self, node: AstNodeRef<ast::FnTy>) -> Result<Self::FnTyRet, Self::Error> {
        // This will be filled in during resolution
        let fn_ty_id = self.new_ty(FnTy {
            implicit: false,
            is_unsafe: false,
            params: self.create_hole_params_from(&node.params, |params| &params.name),
            pure: true,
            return_ty: self.new_ty_hole(),
        });

        // Traverse the function body
        self.enter_item(node, fn_ty_id, || walk::walk_fn_ty(self, node))?;

        Ok(())
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
