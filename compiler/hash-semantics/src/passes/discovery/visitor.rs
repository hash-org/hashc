//! AST visitor for the discovery pass.

use hash_ast::{
    ast::{self, AstNodeRef},
    ast_visitor_default_impl,
    visitor::walk,
};
use hash_reporting::{diagnostic::Diagnostics, macros::panic_on_span};
use hash_storage::store::statics::SequenceStoreValue;
use hash_tir::{
    data::DataDef,
    environment::env::AccessToEnv,
    fns::{FnBody, FnDef, FnTy},
    mods::{ModDef, ModKind, ModMember},
    node::{Node, NodeOrigin},
    scopes::Stack,
    symbols::SymbolId,
    terms::Term,
    tuples::TupleTy,
    tys::Ty,
    utils::AccessToUtils,
};
use hash_utils::itertools::Itertools;

use super::{
    defs::{DefId, ItemId},
    DiscoveryPass,
};
use crate::{
    diagnostics::error::SemanticError, environment::sem_env::AccessToSemEnv,
    passes::ast_utils::AstPass,
};

impl<'tc> ast::AstVisitor for DiscoveryPass<'tc> {
    type Error = SemanticError;
    ast_visitor_default_impl!(
        hiding: Declaration,
        Module,
        ModDef,
        TraitDef,
        StructDef,
        EnumDef,
        FnDef,
        FnTy,
        TyFnTy,
        TyFnDef,
        TupleTy,
        BodyBlock,
        Expr,
        MatchCase,
        Import
    );

    type DeclarationRet = ();
    fn visit_declaration(
        &self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let walk_with_name_hint = || -> Result<_, Self::Error> {
            let name = match node.pat.body() {
                ast::Pat::Binding(binding) => Some(SymbolId::from_name(
                    binding.name.ident,
                    NodeOrigin::Given(binding.name.id()),
                )),
                // If the pattern is not a binding, we don't know the name of the declaration
                _ => None,
            };
            // Walk the node
            self.name_hint.enter(name, || walk::walk_declaration(self, node))?;
            Ok(name)
        };

        // Add the declaration to the current definition as appropriate
        match self.get_current_item() {
            Some(ItemId::Def(def_id)) => match def_id {
                DefId::Mod(mod_def_id) => {
                    let name = walk_with_name_hint()?;
                    match name {
                        Some(name) => self.add_declaration_node_to_mod_def(name, node, mod_def_id),
                        None => {
                            return Err(SemanticError::ModulePatternsNotSupported {
                                location: node.span(),
                            })
                        }
                    }
                }
                DefId::Data(_) => {
                    panic_on_span!(
                        node.span(),
                        "found declaration in data definition scope, which should have been handled earlier"
                    )
                }
                DefId::Stack(stack_id) => {
                    let name = walk_with_name_hint()?;

                    // If we can add the declaration as a mod member, do so.
                    if self.stack_declaration_is_mod_member(node) {
                        let mod_member = self
                            .make_mod_member_data_from_declaration_node(name.unwrap(), node)
                            .unwrap();
                        self.add_mod_member_to_stack(stack_id, node.id(), mod_member)
                    } else {
                        self.add_pat_node_binds_to_stack(
                            node.pat.ast_ref(),
                            stack_id,
                            name,
                            node.value.as_ref(),
                        );
                    }
                }
                DefId::Fn(_) => {
                    panic_on_span!(
                        node.span(),
                        "found declaration in function scope, which should instead be in a stack scope"
                    )
                }
            },
            Some(ItemId::Ty(_)) => {
                panic_on_span!(
                        node.span(),
                        "found declaration in function type scope, which should instead be in a stack scope"
                    )
            }
            None => {
                panic_on_span!(node.span(), "found declaration before any scopes")
            }
        };

        Ok(())
    }

    type MatchCaseRet = ();
    fn visit_match_case(
        &self,
        node: AstNodeRef<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        // A match case creates its own stack scope.
        let stack_id = Stack::empty(NodeOrigin::Given(node.id()));
        self.enter_def(node, stack_id, || {
            self.add_pat_node_binds_to_stack(node.pat.ast_ref(), stack_id, None, Some(&node.expr));
            walk::walk_match_case(self, node)
        })?;
        Ok(())
    }

    type ModuleRet = ();
    fn visit_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let source_id = self.current_source_info().source_id();
        let mod_def_id = self.mod_utils().create_or_get_module_mod_def(source_id.into());

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
        let mod_block_name = self.take_name_hint_or_create_internal_name(node.id());

        // @@Todo: error if the mod block has generics

        // Create a mod block definition, with empty members for now.
        let mod_def_id = Node::create_at(
            ModDef {
                name: mod_block_name,
                kind: ModKind::ModBlock,
                members: Node::create_at(
                    Node::<ModMember>::empty_seq(),
                    NodeOrigin::Given(node.block.id()),
                ),
            },
            NodeOrigin::Given(node.id()),
        );

        // Traverse the mod block
        self.enter_def(node, mod_def_id, || walk::walk_mod_def(self, node))?;

        Ok(())
    }

    type StructDefRet = ();
    fn visit_struct_def(
        &self,
        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let struct_name = self.take_name_hint_or_create_internal_name(node.id());

        // Create a data definition for the struct
        let struct_def_id = DataDef::struct_def(
            struct_name,
            self.create_hole_params_from_ty_params(node.ty_params.as_ref(), node.id()),
            self.create_hole_params_from_params(Some(&node.fields), node.fields.id()),
            NodeOrigin::Given(node.id()),
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
        let enum_name = self.take_name_hint_or_create_internal_name(node.id());

        // Create a data definition for the enum
        let enum_def_id = DataDef::indexed_enum_def(
            enum_name,
            self.create_hole_params_from_ty_params(node.ty_params.as_ref(), node.id()),
            |_| {
                Node::at(
                    node.entries
                        .iter()
                        .map(|variant| {
                            Node::at(
                                (
                                    SymbolId::from_name(
                                        variant.name.ident,
                                        NodeOrigin::Given(variant.name.id()),
                                    ),
                                    self.create_hole_params_from_params(
                                        variant.fields.as_ref(),
                                        variant.id(),
                                    ),
                                    None,
                                ),
                                NodeOrigin::Given(variant.id()),
                            )
                        })
                        .collect_vec(),
                    NodeOrigin::Given(node.entries.id()),
                )
            },
            NodeOrigin::Given(node.id()),
        );

        // Traverse the enum; the variants have already been created.
        self.enter_item(node, ItemId::Def(enum_def_id.into()), || walk::walk_enum_def(self, node))?;

        Ok(())
    }

    type FnDefRet = ();
    fn visit_fn_def(&self, node: AstNodeRef<ast::FnDef>) -> Result<Self::FnDefRet, Self::Error> {
        // Get the function name from the name hint.
        let fn_def_name = self.take_name_hint_or_create_internal_name(node.id());

        // Create a function definition
        let fn_def_id = Node::create_at(
            FnDef {
                name: fn_def_name,
                body: FnBody::Defined(Term::hole(NodeOrigin::Given(node.fn_body.id()))),
                ty: FnTy {
                    implicit: false,
                    is_unsafe: false,
                    params: self
                        .create_hole_params_from_params(Some(&node.params), node.params.id()),
                    pure: false,
                    return_ty: node
                        .return_ty
                        .as_ref()
                        .map(|ty| Ty::hole(NodeOrigin::Given(ty.id())))
                        .unwrap_or_else(|| Ty::hole(NodeOrigin::InferredFrom(node.fn_body.id()))),
                },
            },
            NodeOrigin::Given(node.id()),
        );

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
        let fn_def_name = self.take_name_hint_or_create_internal_name(node.id());

        // Create a function definition
        let fn_def_id = Node::create_at(
            FnDef {
                name: fn_def_name,
                body: FnBody::Defined(Term::hole(NodeOrigin::Given(node.ty_fn_body.id()))),
                ty: FnTy {
                    implicit: true,
                    is_unsafe: false,
                    params: self
                        .create_hole_params_from_ty_params(Some(&node.params), node.params.id()),
                    pure: true,
                    return_ty: node
                        .return_ty
                        .as_ref()
                        .map(|ty| Ty::hole(NodeOrigin::Given(ty.id())))
                        .unwrap_or_else(|| {
                            Ty::hole(NodeOrigin::InferredFrom(node.ty_fn_body.id()))
                        }),
                },
            },
            NodeOrigin::Given(node.id()),
        );

        // Traverse the function body
        self.enter_def(node, fn_def_id, || walk::walk_ty_fn_def(self, node))?;

        Ok(())
    }

    type BodyBlockRet = ();
    fn visit_body_block(
        &self,
        node: AstNodeRef<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        let origin = NodeOrigin::Given(node.id());
        match self.get_current_item() {
            Some(ItemId::Def(def_id)) => match def_id {
                // If we are in a mod or data block, this isn't a stack scope so we don't do anything.
                DefId::Mod(_) | DefId::Data(_) => {
                    walk::walk_body_block(self, node)?;
                    Ok(())
                }
                // If we are in a stack scope, this is a nested block, so we add a new stack
                DefId::Stack(_) |
                // If we are in a function, then this is the function's body, so we add a new stack
                DefId::Fn(_) => {
                    let stack_id = Stack::empty(origin);
                    self.enter_def(node, stack_id, || walk::walk_body_block(self, node))?;
                    Ok(())
                }
            },
            Some(ItemId::Ty(_)) => {
                // If we are in a function type, then this is the function's type return, so we
                // add a new stack
                let stack_id = Stack::empty(origin);
                self.enter_def(node, stack_id, || walk::walk_body_block(self, node))?;
                Ok(())
            }
            None => {
                // This is a root scope for interactive, so we add a new stack
                let stack_id = Stack::empty(origin);
                self.enter_def(node, stack_id, || walk::walk_body_block(self, node))?;
                Ok(())
            }
        }
    }

    type TyFnTyRet = ();
    fn visit_ty_fn_ty(
        &self,
        node: AstNodeRef<ast::TyFnTy>,
    ) -> Result<Self::TyFnTyRet, Self::Error> {
        // This will be filled in during resolution
        let fn_ty_id = Ty::from(
            FnTy {
                implicit: true,
                is_unsafe: false,
                params: self
                    .create_hole_params_from_ty_params(Some(&node.params), node.params.id()),
                pure: true,
                return_ty: Ty::hole(NodeOrigin::Given(node.return_ty.id())),
            },
            NodeOrigin::Given(node.id()),
        );

        // Traverse the type function body
        self.enter_item(node, fn_ty_id, || walk::walk_ty_fn_ty(self, node))?;

        Ok(())
    }

    type FnTyRet = ();
    fn visit_fn_ty(&self, node: AstNodeRef<ast::FnTy>) -> Result<Self::FnTyRet, Self::Error> {
        // This will be filled in during resolution
        let fn_ty_id = Ty::from(
            FnTy {
                implicit: false,
                is_unsafe: false,
                params: self.create_hole_params_from_params(Some(&node.params), node.params.id()),
                pure: false,
                return_ty: Ty::hole(NodeOrigin::Given(node.return_ty.id())),
            },
            NodeOrigin::Given(node.id()),
        );

        // Traverse the function body
        self.enter_item(node, fn_ty_id, || walk::walk_fn_ty(self, node))?;

        Ok(())
    }

    type TupleTyRet = ();
    fn visit_tuple_ty(
        &self,
        node: AstNodeRef<ast::TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        // This will be filled in during resolution
        let tuple_ty_id = Ty::from(
            TupleTy {
                data: self.create_hole_params_from_params(Some(&node.entries), node.entries.id()),
            },
            NodeOrigin::Given(node.id()),
        );

        // Traverse the tuple body
        self.enter_item(node, tuple_ty_id, || walk::walk_tuple_ty(self, node))?;

        Ok(())
    }

    type TraitDefRet = ();
    fn visit_trait_def(
        &self,
        node: ast::AstNodeRef<ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        // Traits are not yet supported
        self.diagnostics()
            .add_error(SemanticError::TraitsNotSupported { trait_location: node.span() });
        Ok(())
    }

    type ExprRet = ();
    fn visit_expr(&self, node: AstNodeRef<ast::Expr>) -> Result<Self::ExprRet, Self::Error> {
        match node.body {
            ast::Expr::StructDef(_)
            | ast::Expr::EnumDef(_)
            | ast::Expr::TyFnDef(_)
            | ast::Expr::TraitDef(_)
            | ast::Expr::ImplDef(_)
            | ast::Expr::ModDef(_)
            | ast::Expr::FnDef(_)
            | ast::Expr::TraitImpl(_)
            | ast::Expr::Macro(_) => {} // These accept a name hint
            _ => {
                // Everything else should not have a name hint
                self.name_hint.take();
            }
        }
        walk::walk_expr(self, node)?;
        Ok(())
    }

    type ImportRet = ();
    fn visit_import(&self, node: AstNodeRef<ast::Import>) -> Result<Self::ImportRet, Self::Error> {
        self.current_source_info()
            .with_source_id(node.source, || DiscoveryPass::new(self.sem_env()).pass_source())?;
        Ok(())
    }
}
