use std::{collections::HashMap, fmt};

/// The second pass of the typechecker, which resolves all symbols to their
/// referenced bindings.
///
/// Any scoping errors are reported here.
use hash_ast::{
    ast::{self, AstNodeRef},
    ast_visitor_default_impl,
    visitor::{walk, AstVisitor},
};
use hash_source::{identifier::Identifier, location::Span};
use hash_types::new::{
    access::AccessTerm,
    environment::{context::ScopeKind, env::AccessToEnv},
    locations::LocationTarget,
    scopes::StackMemberId,
    symbols::Symbol,
    terms::Term,
};
use hash_utils::{
    state::{HeavyState, LightState},
    store::{CloneStore, SequenceStore, Store},
};

use self::ast_paths::*;
use super::ast_pass::AstPass;
use crate::{
    impl_access_to_tc_env,
    new::{
        diagnostics::error::{TcError, TcResult},
        environment::tc_env::{AccessToTcEnv, TcEnv, WithTcEnv},
        ops::{ast::AstOps, common::CommonOps, AccessToOps},
    },
};

pub mod ast_paths;
pub mod exprs;
pub mod pats;
pub mod tys;

/// The current expression kind we are in.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InExpr {
    /// We are in a type expression.
    Ty,
    /// We are in a value expression.
    Value,
    /// We are in a pattern.
    Pat,
}

/// The kind of context we are in.
///
/// Either we are trying to resolve a symbol in the environment, or we are
/// trying to resolve a symbol through access of another term.
#[derive(Copy, Clone, Debug)]
pub enum ContextKind {
    /// An access context, where we are trying to resolve a symbol through
    /// access of another term.
    ///
    /// The tuple contains the identifier accessing from and the location target
    /// of the definition .
    Access(NonTerminalResolvedPathComponent, LocationTarget),
    /// Just the current scope.
    Environment,
}

impl fmt::Display for WithTcEnv<'_, &ContextKind> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            ContextKind::Access(non_terminal, _loc) => {
                write!(f, "{}", self.tc_env().with(non_terminal))
            }
            ContextKind::Environment => write!(f, "the current scope"),
        }
    }
}

/// The second pass of the typechecker, which resolves all symbols to their
/// referenced bindings.
pub struct SymbolResolutionPass<'tc> {
    tc_env: &'tc TcEnv<'tc>,
    in_expr: LightState<InExpr>,
    /// Stores a list of contexts we are in, mirroring `ContextStore` but with
    /// identifiers so that we can resolve them to symbols.
    ///
    /// Also keeps track of the kind of context we are in.
    bindings_by_name: HeavyState<Vec<(ContextKind, HashMap<Identifier, Symbol>)>>,
}

impl_access_to_tc_env!(SymbolResolutionPass<'tc>);

impl<'tc> AstPass for SymbolResolutionPass<'tc> {
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

/// This block contains general helper functions for traversing scopes and
/// adding bindings.
impl<'tc> SymbolResolutionPass<'tc> {
    pub fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        Self {
            tc_env,
            in_expr: LightState::new(InExpr::Value),
            bindings_by_name: HeavyState::new(Vec::new()),
        }
    }

    /// Find a binding by name, returning the symbol of the binding.
    ///
    /// This will search the current scope and all parent scopes.
    /// If the binding is not found, it will return `None`.
    ///
    /// Will panic if there are no scopes in the context.
    fn get_current_context_kind(&self) -> ContextKind {
        self.bindings_by_name.get().last().unwrap().0
    }

    /// Find a binding by name, returning the symbol of the binding.
    ///
    /// This will search the current scope and all parent scopes.
    /// If the binding is not found, it will return `None`.
    fn lookup_binding_by_name(&self, name: Identifier) -> Option<Symbol> {
        self.bindings_by_name.get().iter().rev().find_map(|b| b.1.get(&name).copied())
    }

    /// Find a binding by name, returning the symbol of the binding.
    ///
    /// Errors if the binding is not found.
    ///
    /// See [`SymbolResolutionPass::lookup_binding_by_name()`].
    fn lookup_binding_by_name_or_error(
        &self,
        name: Identifier,
        span: Span,
        looking_in: ContextKind,
    ) -> TcResult<Symbol> {
        self.lookup_binding_by_name(name).ok_or_else(|| TcError::SymbolNotFound {
            symbol: self.new_symbol(name),
            location: self.source_location(span),
            looking_in,
        })
    }

    /// Run a function in a new scope, and then exit the scope.
    ///
    /// In addition to adding the appropriate bindings, this also adds the
    /// appropriate names to `bindings_by_name`.
    fn enter_scope<T>(
        &self,
        kind: ScopeKind,
        context_kind: ContextKind,
        f: impl FnOnce() -> T,
    ) -> T {
        self.context_ops().enter_scope(kind, || {
            self.bindings_by_name.enter(
                |b| {
                    let current_level = self.context().get_current_scope_level();

                    // Populate the map with all the bindings in the current
                    // scope. Any duplicate names will be shadowed by the last entry.
                    let mut map = HashMap::new();
                    self.context().for_bindings_of_level(current_level, |binding| {
                        let symbol_data = self.stores().symbol().get(binding.name);
                        if let Some(name) = symbol_data.name {
                            map.insert(name, binding.name);
                        }
                    });

                    b.push((context_kind, map));
                },
                |b| {
                    // Exit the scope on the context exit.
                    b.pop();
                },
                f,
            )
        })
    }

    /// Add a stack member to the current scope, also adding it to the
    /// `bindings_by_name` map.
    fn add_stack_binding(&self, member_id: StackMemberId) {
        // Get the data of the member.
        let member_name =
            self.stores().stack().map_fast(member_id.0, |stack| stack.members[member_id.1].name);
        let member_name_data = self.stores().symbol().get(member_name);

        // Add the binding to the current scope.
        self.context_ops().add_stack_binding(member_id);

        // Add the binding to the `bindings_by_name` map.
        if let Some(name) = member_name_data.name {
            match self.bindings_by_name.get_mut().last_mut() {
                Some(bindings) => {
                    bindings.1.insert(name, member_name);
                }
                None => panic!("No bindings_by_name map for current scope!"),
            }
        }
    }

    /// Run a function for each stack member in the given pattern.
    ///
    /// The stack members are found in the `AstInfo` store, specifically the
    /// `stack_members` map. They are looked up using the IDs of the pattern
    /// binds, as added by the `add_stack_members_in_pat_to_buf` method of the
    /// `ScopeDiscoveryPass`.
    fn for_each_stack_member_of_pat(
        &self,
        node: ast::AstNodeRef<ast::Pat>,
        f: impl Fn(StackMemberId) + Copy,
    ) {
        let for_spread_pat = |spread: &ast::AstNode<ast::SpreadPat>| {
            if let Some(name) = &spread.name {
                if let Some(member_id) =
                    self.ast_info().stack_members().get_data_by_node(name.ast_ref().id())
                {
                    f(member_id);
                }
            }
        };
        match node.body() {
            ast::Pat::Binding(_) => {
                if let Some(member_id) = self.ast_info().stack_members().get_data_by_node(node.id())
                {
                    f(member_id);
                }
            }
            ast::Pat::Tuple(tuple_pat) => {
                for (index, entry) in tuple_pat.fields.ast_ref_iter().enumerate() {
                    if let Some(spread_node) = &tuple_pat.spread && spread_node.position == index {
                        for_spread_pat(spread_node);
                    }
                    self.for_each_stack_member_of_pat(entry.pat.ast_ref(), f);
                }
            }
            ast::Pat::Constructor(constructor_pat) => {
                for (index, field) in constructor_pat.fields.ast_ref_iter().enumerate() {
                    if let Some(spread_node) = &constructor_pat.spread && spread_node.position == index {
                        for_spread_pat(spread_node);
                    }
                    self.for_each_stack_member_of_pat(field.pat.ast_ref(), f);
                }
            }
            ast::Pat::List(list_pat) => {
                for (index, pat) in list_pat.fields.ast_ref_iter().enumerate() {
                    if let Some(spread_node) = &list_pat.spread && spread_node.position == index {
                        for_spread_pat(spread_node);
                    }
                    self.for_each_stack_member_of_pat(pat, f);
                }
            }
            ast::Pat::Or(or_pat) => {
                if let Some(pat) = or_pat.variants.get(0) {
                    self.for_each_stack_member_of_pat(pat.ast_ref(), f)
                }
            }
            ast::Pat::If(if_pat) => self.for_each_stack_member_of_pat(if_pat.pat.ast_ref(), f),
            ast::Pat::Wild(_) => {
                if let Some(member_id) = self.ast_info().stack_members().get_data_by_node(node.id())
                {
                    f(member_id);
                }
            }
            ast::Pat::Module(_) | ast::Pat::Access(_) | ast::Pat::Lit(_) | ast::Pat::Range(_) => {}
        }
    }
}

/// This visitor resolves all symbols and paths in the AST.
impl ast::AstVisitor for SymbolResolutionPass<'_> {
    type Error = TcError;
    ast_visitor_default_impl!(
        hiding: Module,
        Declaration,
        ModDef,
        StructDef,
        EnumDef,
        FnDef,
        TyFnDef,
        BodyBlock,
        MatchCase,
        Expr,
        AccessExpr,
        ConstructorCallExpr,
        VariableExpr,
        Ty,
        AccessTy,
        NamedTy,
        TyFnCall,
        AccessPat,
        ConstructorPat,
    );

    type ModuleRet = ();
    fn visit_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Mod(mod_def_id), ContextKind::Environment, || {
            walk::walk_module(self, node)
        })?;
        Ok(())
    }

    type ModDefRet = ();
    fn visit_mod_def(
        &self,
        node: ast::AstNodeRef<ast::ModDef>,
    ) -> Result<Self::ModDefRet, Self::Error> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Mod(mod_def_id), ContextKind::Environment, || {
            walk::walk_mod_def(self, node)
        })?;
        Ok(())
    }

    type StructDefRet = ();
    fn visit_struct_def(
        &self,
        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let data_def_id = self.ast_info().data_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Data(data_def_id), ContextKind::Environment, || {
            walk::walk_struct_def(self, node)
        })?;
        Ok(())
    }

    type EnumDefRet = ();
    fn visit_enum_def(
        &self,
        node: ast::AstNodeRef<ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let data_def_id = self.ast_info().data_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Data(data_def_id), ContextKind::Environment, || {
            walk::walk_enum_def(self, node)
        })?;
        Ok(())
    }

    type FnDefRet = ();
    fn visit_fn_def(
        &self,
        node: ast::AstNodeRef<ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        let fn_def_id = self.ast_info().fn_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Fn(fn_def_id), ContextKind::Environment, || {
            walk::walk_fn_def(self, node)
        })?;
        Ok(())
    }

    type TyFnDefRet = ();
    fn visit_ty_fn_def(
        &self,
        node: ast::AstNodeRef<ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let fn_def_id = self.ast_info().fn_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Fn(fn_def_id), ContextKind::Environment, || {
            walk::walk_ty_fn_def(self, node)
        })?;
        Ok(())
    }

    type BodyBlockRet = ();
    fn visit_body_block(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        match self.ast_info().stacks().get_data_by_node(node.id()) {
            Some(stack_id) => {
                // This is a stack, so we need to enter its scope.
                self.enter_scope(ScopeKind::Stack(stack_id), ContextKind::Environment, || {
                    walk::walk_body_block(self, node)?;
                    Ok(())
                })?;
            }
            None => {
                // This is not a stack, so it must be some other block handled
                // elsewhere.
                walk::walk_body_block(self, node)?;
            }
        };
        Ok(())
    }

    type DeclarationRet = ();
    fn visit_declaration(
        &self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        // If we are in a stack, then we need to add the declaration to the
        // stack's scope. Otherwise the declaration is handled higher up.
        if let ScopeKind::Stack(_) = self.context().get_current_scope_kind() {
            self.for_each_stack_member_of_pat(node.pat.ast_ref(), |member| {
                self.add_stack_binding(member);
            });
        }
        walk::walk_declaration(self, node)?;
        Ok(())
    }

    type MatchCaseRet = ();
    fn visit_match_case(
        &self,
        node: ast::AstNodeRef<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let stack_id = self.ast_info().stacks().get_data_by_node(node.id()).unwrap();
        // Each match case has its own scope, so we need to enter it, and add all the
        // pattern bindings to the context.
        self.enter_scope(ScopeKind::Stack(stack_id), ContextKind::Environment, || {
            self.for_each_stack_member_of_pat(node.pat.ast_ref(), |member| {
                self.add_stack_binding(member);
            });
            walk::walk_match_case(self, node)?;
            Ok(())
        })
    }

    type TyRet = ();
    fn visit_ty(&self, node: ast::AstNodeRef<ast::Ty>) -> Result<Self::TyRet, Self::Error> {
        self.in_expr.enter(InExpr::Ty, || {
            walk::walk_ty(self, node)?;
            // For each node, try to resolve it as an ast path. If it is an ast path,
            // it is added to the node.
            match self.ty_as_ast_path(node) {
                Ok(Some(path)) => {
                    // Resolve the path, which which adds it to the node.
                    match self.resolve_ast_path(&path, node) {
                        Ok(_) => {}
                        Err(err) => {
                            self.diagnostics().add_error(err);
                        }
                    }
                }
                Ok(None) => {}
                Err(err) => {
                    self.diagnostics().add_error(err);
                }
            };
            Ok(())
        })?;
        Ok(())
    }

    type ExprRet = ();
    fn visit_expr(&self, node: ast::AstNodeRef<ast::Expr>) -> Result<Self::ExprRet, Self::Error> {
        if let ContextKind::Access(_, _) = self.get_current_context_kind() {
            // Handled by path resolution.
            return Ok(());
        }

        self.in_expr.enter(InExpr::Value, || {
            walk::walk_expr(self, node)?;
            // For each node, try to resolve it as an ast path. If it is an ast path,
            // it is added to the node.
            match self.expr_as_ast_path(node) {
                Ok(Some(path)) => {
                    // Resolve the path, which which adds it to the node.
                    match self.resolve_ast_path(&path, node) {
                        Ok(_) => {}
                        Err(err) => {
                            self.diagnostics().add_error(err);
                        }
                    }
                }
                Ok(None) => {}
                Err(err) => {
                    self.diagnostics().add_error(err);
                }
            };
            Ok(())
        })
    }

    type AccessPatRet = ();
    fn visit_access_pat(
        &self,
        _node: ast::AstNodeRef<ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        // @@Todo
        Ok(())
    }

    type ConstructorPatRet = ();
    fn visit_constructor_pat(
        &self,
        _node: AstNodeRef<ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        // @@Todo
        Ok(())
    }

    type AccessExprRet = ();
    fn visit_access_expr(
        &self,
        node: ast::AstNodeRef<ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        let path = self.access_expr_as_ast_path(node)?;
        match path {
            Some(_) => {
                // Will be handled by path resolution.
            }
            None => {
                // This is just a property access, so we create it here:
                walk::walk_access_expr(self, node)?;

                // @@Correctness: Might need to match instead of unwrap?
                let subject = self.ast_info().terms().get_data_by_node(node.subject.id()).unwrap();
                let access_term = self
                    .new_term(Term::Access(AccessTerm { subject, field: (*node.property).into() }));
                self.ast_info().terms().insert(node.id(), access_term);
            }
        }
        Ok(())
    }

    type TyFnCallRet = ();
    fn visit_ty_fn_call(
        &self,
        node: AstNodeRef<ast::TyFnCall>,
    ) -> Result<Self::TyFnCallRet, Self::Error> {
        // Do not visit the body, because the path resolution will handle it.
        for arg in node.args.iter() {
            self.visit_ty_arg(arg.ast_ref())?;
        }
        Ok(())
    }

    type NamedTyRet = ();
    fn visit_named_ty(
        &self,
        _node: AstNodeRef<ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        // Handled by path resolution.
        Ok(())
    }

    type AccessTyRet = ();
    fn visit_access_ty(
        &self,
        _node: AstNodeRef<ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        // Handled by path resolution.
        Ok(())
    }

    type ConstructorCallExprRet = ();
    fn visit_constructor_call_expr(
        &self,
        node: AstNodeRef<ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        // Do not visit the body, because the path resolution will handle it.
        for arg in node.args.iter() {
            self.visit_constructor_call_arg(arg.ast_ref())?;
        }
        Ok(())
    }

    type VariableExprRet = ();
    fn visit_variable_expr(
        &self,
        _node: AstNodeRef<ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        // Handled by path resolution.
        Ok(())
    }
}
