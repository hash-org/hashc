//! Visitor for scope checking on the AST.
//!
//! This module is responsible for performing scoping analysis on the Hash AST.
//! This includes:
//! - Resolving all names to their corresponding definitions.
//! - Gathering scopes of definitions and indexing them by AST node IDs.
//! - Checking for recursive definitions.
//! - Ensuring that there are no free variables in the AST.
use hash_ast::{
    ast::{
        self, AccessExpr, AccessPat, AccessTy, AstNode, AstNodeId, AstNodeRef, BindingPat,
        BodyBlock, CallExpr, ConstructorPat, Declaration, EnumDef, ExprArg, FnDef, FnTy,
        ImplicitFnCall, ImplicitFnDef, MatchCase, ModDef, Module, ModulePatEntry, NamedTy,
        OwnsAstNode, Param, Params, StructDef, TuplePat, TupleTy, TyArg, TyParam, TyParams,
        VariableExpr,
    },
    ast_visitor_mut_self_default_impl,
    node_map::SourceRef,
    visitor::{walk_mut_self, AstVisitorMutSelf},
};
use hash_reporting::diagnostic::{DiagnosticStore, HasDiagnosticsMut};

use crate::{
    diagnostics::{ScopingDiagnostics, ScopingError},
    scope::{Scope, ScopeData, ScopeMember},
};

/// The mode of visiting scopes.
///
/// The visitor operates in three separate passes shown below.
/// This is so that out-of-order references can be resolved.
///
/// Definitions (structs/enums/modules) are discovered separately from
/// other declarations, because they might appear inside patterns, so there
/// needs to be a way of differentiating between a pattern binding and a
/// pattern that refers to a definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ScopeVisitMode {
    /// Find all definitions, including struct/enum/module definitions.
    DiscoverDefinitions,
    /// Find all declarations, including variable declarations, and resolve
    /// references to definitions.
    DiscoverDeclarations,
    /// Resolve all references to declarations.
    ResolveReferences,
}

/// Visitor for scope checking on the AST.
pub(crate) struct ScopeCheckVisitor<'n> {
    /// What mode the visitor is in.
    pub(crate) mode: ScopeVisitMode,
    /// The stack of scopes that the visitor is currently in.
    pub(crate) current_scopes: Vec<AstNodeId>,
    /// The scope data that the visitor is writing to.
    pub(crate) scope_data: &'n mut ScopeData,
    /// The diagnostics for the scope checker.
    pub(crate) diagnostics: ScopingDiagnostics,
}

impl HasDiagnosticsMut for ScopeCheckVisitor<'_> {
    type Diagnostics = ScopingDiagnostics;
    fn diagnostics(&mut self) -> &mut Self::Diagnostics {
        &mut self.diagnostics
    }
}

impl ScopeCheckVisitor<'_> {
    /// Run the scope checking pass on a source, storing the result in the given
    /// `ScopeData`.
    pub(crate) fn run_on_source<'s>(
        entry_point_source: SourceRef,
        scope_data: &'s mut ScopeData,
    ) -> ScopeCheckVisitor<'s> {
        let modes = [
            ScopeVisitMode::DiscoverDefinitions,
            ScopeVisitMode::DiscoverDeclarations,
            ScopeVisitMode::ResolveReferences,
        ];
        let mut visitor = ScopeCheckVisitor {
            mode: modes[0],
            current_scopes: Vec::new(),
            scope_data,
            diagnostics: DiagnosticStore::new(),
        };
        for mode in modes.iter() {
            visitor.mode = *mode;
            visitor.visit_source(entry_point_source);
        }
        visitor
    }

    /// Visit a source and check its scopes.
    fn visit_source(&mut self, source: SourceRef) {
        match source {
            SourceRef::Interactive(interactive) => {
                let node = interactive.node();
                self.visit_body_block(node.ast_ref()).into_ok();
            }
            SourceRef::Module(module) => {
                let node = module.node();
                self.visit_module(node.ast_ref()).into_ok();
            }
        }
    }

    /// Get the current scope, if there is one.
    fn maybe_current_scope_mut(&mut self) -> Option<&mut Scope> {
        let id = *self.current_scopes.last()?;
        self.scope_data.get_scope_mut(id)
    }

    /// Get the current scope.
    fn current_scope_mut(&mut self) -> &mut Scope {
        self.maybe_current_scope_mut().unwrap()
    }

    /// Register a reference if it is found and `accept_origin(member) = true`,
    /// otherwise run the given function.
    fn register_reference_or_else(
        &mut self,
        name: &AstNode<ast::Name>,
        accept_origin: impl Fn(&ScopeMember) -> bool,
        otherwise: impl FnOnce(&mut Self),
    ) {
        // First try to find the definition in the current scopes.
        let mut found = false;
        for scope_id in self.current_scopes.iter().rev() {
            let scope = self.scope_data.get_existing_scope_mut(*scope_id);
            if let Some(member) = scope.get_member_mut(name.ident) && accept_origin(member) {
                member.add_referencing_node(name.id());
                found = true;
                break;
            }
        }

        if !found {
            otherwise(self);
        }
    }

    /// Register a definition.
    ///
    /// Runs in `DiscoverDefinitions` mode.
    fn register_definition(&mut self, name: &AstNode<ast::Name>) {
        if self.mode == ScopeVisitMode::DiscoverDefinitions {
            let scope = self.current_scope_mut();
            scope.register_member(name.id(), name.ident)
        }
    }

    /// Register a reference if it is found, otherwise report an error.
    ///
    /// Runs in `ResolveReferences` mode.
    fn register_reference_or_error(&mut self, name: &AstNode<ast::Name>) {
        if self.mode == ScopeVisitMode::ResolveReferences {
            self.register_reference_or_else(
                name,
                |_| true,
                |this| {
                    // If it's not found, then report an error.
                    this.add_error(ScopingError::SymbolNotFound {
                        symbol: name.ident,
                        referencing_node: name.id(),
                    })
                },
            )
        }
    }

    /// Register a definition reference if it is found, otherwise declare a
    /// new variable. Runs in `DiscoverDeclarations` mode.
    ///
    /// This is meant to be used for `BindingPat`, which might refer to an
    /// existing struct/enum, or declare a new variable.
    fn register_definition_reference_or_declare(&mut self, name: &AstNode<ast::Name>) {
        if self.mode == ScopeVisitMode::DiscoverDeclarations {
            self.register_reference_or_else(
                name,
                |_| true, // @@Todo: do not accept if it is just a variable
                |this| {
                    // If it's not found, then it's a definition.
                    let scope = this.current_scope_mut();
                    scope.register_member(name.id(), name.ident)
                },
            )
        }
    }

    /// Enter a scope, creating it if it does not exist.
    fn enter_scope<T>(&mut self, node: AstNodeId, f: impl FnOnce(&mut Self) -> T) -> T {
        let current_scope_node = self.maybe_current_scope_mut().map(|scope| scope.node());
        self.scope_data.insert_scope_if_does_not_exist(node, || match current_scope_node {
            Some(parent) => Scope::child(node, parent),
            None => Scope::root(node),
        });
        self.enter_existing_scope(node, f)
    }

    /// Enter an existing scope.
    fn enter_existing_scope<T>(&mut self, node: AstNodeId, f: impl FnOnce(&mut Self) -> T) -> T {
        assert!(self.scope_data.get_scope(node).is_some());
        self.current_scopes.push(node);
        let result = f(self);
        self.current_scopes.pop();
        result
    }
}

impl hash_ast::ast::AstVisitorMutSelf for ScopeCheckVisitor<'_> {
    type Error = !;

    ast_visitor_mut_self_default_impl!(
      hiding: VariableExpr, BodyBlock, Params, TyParams, Param, TyParam, TyArg, ExprArg, StructDef,
      EnumDef, ImplicitFnDef, ModDef, FnDef, Module, TupleLit, TupleTy, FnTy, NamedTy, ImplicitFn,
      AccessTy, AccessExpr, Declaration, CallExpr, ImplicitFnCall, MatchCase, BindingPat,
      AccessPat, TuplePat, ConstructorPat, ModulePatEntry
    );

    // Definitions:
    type ParamRet = ();
    fn visit_param(&mut self, node: AstNodeRef<Param>) -> Result<Self::ParamRet, Self::Error> {
        match &node.name {
            Some(name) => self.register_definition(name),
            None => {}
        }
        let _ = walk_mut_self::walk_param(self, node)?;
        Ok(())
    }

    type TyParamRet = ();
    fn visit_ty_param(
        &mut self,
        node: AstNodeRef<TyParam>,
    ) -> Result<Self::TyParamRet, Self::Error> {
        match &node.name {
            Some(name) => self.register_definition(name),
            None => {}
        }
        let _ = walk_mut_self::walk_ty_param(self, node)?;
        Ok(())
    }

    type ExprArgRet = ();
    fn visit_expr_arg(
        &mut self,
        node: AstNodeRef<ExprArg>,
    ) -> Result<Self::ExprArgRet, Self::Error> {
        match &node.name {
            Some(name) => self.register_definition(name),
            None => {}
        }
        let _ = walk_mut_self::walk_expr_arg(self, node)?;
        Ok(())
    }

    type TyArgRet = ();
    fn visit_ty_arg(&mut self, node: AstNodeRef<TyArg>) -> Result<Self::TyArgRet, Self::Error> {
        match &node.name {
            Some(name) => self.register_definition(name),
            None => {}
        }
        let _ = walk_mut_self::walk_ty_arg(self, node)?;
        Ok(())
    }

    type BindingPatRet = ();
    fn visit_binding_pat(
        &mut self,
        node: AstNodeRef<BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        // This is either a definition or a reference.
        self.register_definition_reference_or_declare(&node.name);
        let _ = walk_mut_self::walk_binding_pat(self, node)?;
        Ok(())
    }

    type DeclarationRet = ();
    fn visit_declaration(
        &mut self,
        node: AstNodeRef<Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        match node.value.body() {
            // Definitions.
            ast::Expr::StructDef(_) | ast::Expr::EnumDef(_) | ast::Expr::ModDef(_) => {
                // Specially handle the binding pattern.
                match node.pat.body() {
                    ast::Pat::Binding(binding) => {
                        self.register_definition(&binding.name);
                    }
                    _ => {
                        if self.mode == ScopeVisitMode::DiscoverDefinitions {
                            self.add_error(ScopingError::NonSimpleBindingForDefinition {
                                binding_node: node.pat.id(),
                                definition_node: node.value.id(),
                            });
                        }
                    }
                }

                // Recurse only on the type and value, not the pattern.
                node.ty.as_ref().map(|ty| self.visit_ty(ty.ast_ref()));
                self.visit_expr(node.value.ast_ref())?;
                Ok(())
            }
            // Normal declarations.
            _ => {
                // Recurse normally.
                let _ = walk_mut_self::walk_declaration(self, node)?;
                Ok(())
            }
        }
    }

    // Scopes:

    type BodyBlockRet = ();
    fn visit_body_block(
        &mut self,
        node: AstNodeRef<BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        // Each body block is a new scope that contains the declarations inside it
        // (top-level only).
        self.enter_scope(node.id(), |this| {
            let _ = walk_mut_self::walk_body_block(this, node)?;
            Ok(())
        })
    }

    type MatchCaseRet = ();
    fn visit_match_case(
        &mut self,
        node: AstNodeRef<MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        // Each match case is a new scope that contains the pattern bindings.
        self.enter_scope(node.id(), |this| {
            let _ = walk_mut_self::walk_match_case(this, node)?;
            Ok(())
        })
    }

    type ModuleRet = ();
    fn visit_module(&mut self, node: AstNodeRef<Module>) -> Result<Self::ModuleRet, Self::Error> {
        // Each module is a new scope that contains the module definitions.
        self.enter_scope(node.id(), |this| {
            let _ = walk_mut_self::walk_module(this, node)?;
            Ok(())
        })
    }

    type ParamsRet = ();
    fn visit_params(&mut self, node: AstNodeRef<Params>) -> Result<Self::ParamsRet, Self::Error> {
        // Here we don't enter a new scope, we expect that the parent nodes will do this
        // because sometimes the scope will exceed the parameters (e.g. function types).
        let _ = walk_mut_self::walk_params(self, node)?;
        Ok(())
    }

    type TyParamsRet = ();
    fn visit_ty_params(
        &mut self,
        node: AstNodeRef<TyParams>,
    ) -> Result<Self::TyParamsRet, Self::Error> {
        // Same as above.
        let _ = walk_mut_self::walk_ty_params(self, node)?;
        Ok(())
    }

    type FnTyRet = ();
    fn visit_fn_ty(&mut self, node: AstNodeRef<FnTy>) -> Result<Self::FnTyRet, Self::Error> {
        self.enter_scope(node.id(), |this| {
            let _ = walk_mut_self::walk_fn_ty(this, node)?;
            Ok(())
        })
    }

    type TupleTyRet = ();
    fn visit_tuple_ty(
        &mut self,
        node: AstNodeRef<TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        self.enter_scope(node.id(), |this| {
            let _ = walk_mut_self::walk_tuple_ty(this, node)?;
            Ok(())
        })
    }

    type ImplicitFnDefRet = ();
    fn visit_implicit_fn_def(
        &mut self,
        node: AstNodeRef<ImplicitFnDef>,
    ) -> Result<Self::ImplicitFnDefRet, Self::Error> {
        self.enter_scope(node.id(), |this| {
            let _ = walk_mut_self::walk_implicit_fn_def(this, node)?;
            Ok(())
        })
    }

    type FnDefRet = ();
    fn visit_fn_def(&mut self, node: AstNodeRef<FnDef>) -> Result<Self::FnDefRet, Self::Error> {
        self.enter_scope(node.id(), |this| {
            let _ = walk_mut_self::walk_fn_def(this, node)?;
            Ok(())
        })
    }

    type ModDefRet = ();
    fn visit_mod_def(&mut self, node: AstNodeRef<ModDef>) -> Result<Self::ModDefRet, Self::Error> {
        self.enter_scope(node.id(), |this| {
            let _ = walk_mut_self::walk_mod_def(this, node)?;
            Ok(())
        })
    }

    type StructDefRet = ();
    fn visit_struct_def(
        &mut self,
        node: AstNodeRef<StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        match &node.ty_params {
            Some(params) => {
                self.visit_ty_params(params.ast_ref())?;
            }
            None => {}
        }
        self.enter_scope(node.id(), |this| this.visit_params(node.fields.ast_ref()))
    }

    type EnumDefRet = ();
    fn visit_enum_def(
        &mut self,
        node: AstNodeRef<EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        match &node.ty_params {
            Some(params) => {
                self.visit_ty_params(params.ast_ref())?;
            }
            None => {}
        }
        self.enter_scope(node.id(), |this| {
            for entry in node.entries.ast_ref_iter() {
                this.visit_enum_def_entry(entry)?;
            }
            Ok(())
        })
    }

    // References:

    type VariableExprRet = ();
    fn visit_variable_expr(
        &mut self,
        node: AstNodeRef<VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        self.register_reference_or_error(&node.name);
        let _ = walk_mut_self::walk_variable_expr(self, node)?;
        Ok(())
    }

    type NamedTyRet = ();
    fn visit_named_ty(
        &mut self,
        node: AstNodeRef<NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        self.register_reference_or_error(&node.name);
        let _ = walk_mut_self::walk_named_ty(self, node)?;
        Ok(())
    }

    // @@Todo:

    type AccessPatRet = ();
    fn visit_access_pat(
        &mut self,
        node: AstNodeRef<AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        let _ = walk_mut_self::walk_access_pat(self, node)?;
        Ok(())
    }
    type AccessExprRet = ();
    fn visit_access_expr(
        &mut self,
        node: AstNodeRef<AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        let _ = walk_mut_self::walk_access_expr(self, node)?;
        Ok(())
    }

    type TuplePatRet = ();
    fn visit_tuple_pat(
        &mut self,
        node: AstNodeRef<TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        let _ = walk_mut_self::walk_tuple_pat(self, node)?;
        Ok(())
    }

    type AccessTyRet = ();
    fn visit_access_ty(
        &mut self,
        node: AstNodeRef<AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        let _ = walk_mut_self::walk_access_ty(self, node)?;
        Ok(())
    }

    type ConstructorPatRet = ();
    fn visit_constructor_pat(
        &mut self,
        node: AstNodeRef<ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        let _ = walk_mut_self::walk_constructor_pat(self, node)?;
        Ok(())
    }

    type ModulePatEntryRet = ();
    fn visit_module_pat_entry(
        &mut self,
        node: AstNodeRef<ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error> {
        let _ = walk_mut_self::walk_module_pat_entry(self, node)?;
        Ok(())
    }

    type ImplicitFnCallRet = ();
    fn visit_implicit_fn_call(
        &mut self,
        node: AstNodeRef<ImplicitFnCall>,
    ) -> Result<Self::ImplicitFnCallRet, Self::Error> {
        let _ = walk_mut_self::walk_implicit_fn_call(self, node)?;
        Ok(())
    }

    type CallExprRet = ();
    fn visit_call_expr(
        &mut self,
        node: AstNodeRef<CallExpr>,
    ) -> Result<Self::CallExprRet, Self::Error> {
        let _ = walk_mut_self::walk_call_expr(self, node)?;
        Ok(())
    }
}
