//! General helper functions for traversing scopes and adding bindings.
use std::{collections::HashMap, fmt};

use hash_ast::ast;
use hash_source::{identifier::Identifier, location::Span};
use hash_tir::{
    data::DataDefId,
    environment::{
        context::{ParamOrigin, ScopeKind},
        env::{AccessToEnv, Env},
    },
    fns::FnTy,
    locations::LocationTarget,
    mods::ModDefId,
    params::ParamId,
    scopes::{StackId, StackIndices, StackMemberId},
    symbols::Symbol,
    terms::TermId,
    tuples::TupleTy,
    ty_as_variant,
    utils::{common::CommonUtils, AccessToUtils},
};
use hash_utils::{
    state::HeavyState,
    store::{CloneStore, SequenceStore, SequenceStoreKey, Store},
};

use super::paths::NonTerminalResolvedPathComponent;
use crate::{
    diagnostics::error::{SemanticError, SemanticResult},
    environment::sem_env::{AccessToSemEnv, SemEnv, WithSemEnv},
    passes::ast_utils::AstUtils,
};

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

impl fmt::Display for WithSemEnv<'_, &ContextKind> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            ContextKind::Access(non_terminal, _loc) => {
                write!(f, "`{}`", self.sem_env().with(non_terminal))
            }
            ContextKind::Environment => write!(f, "the current scope"),
        }
    }
}

/// Contains helper functions for traversing scopes and adding bindings.
///
/// It uses [`hash_tir::environment::context::Context`] and
/// [`crate::ops::context::ContextOps`] to enter scopes, but also
/// keeps track of identifier names so that names can be matched to the correct
/// symbols when creating `Var` terms.
pub(super) struct Scoping<'tc> {
    sem_env: &'tc SemEnv<'tc>,
    /// Stores a list of contexts we are in, mirroring `ContextStore` but with
    /// identifiers so that we can resolve them to symbols.
    ///
    /// Also keeps track of the kind of context we are in.
    bindings_by_name: HeavyState<Vec<(ContextKind, HashMap<Identifier, Symbol>)>>,
}

impl AccessToEnv for Scoping<'_> {
    fn env(&self) -> &Env {
        self.sem_env.env()
    }
}

impl AccessToSemEnv for Scoping<'_> {
    fn sem_env(&self) -> &SemEnv<'_> {
        self.sem_env
    }
}

impl<'tc> Scoping<'tc> {
    pub(super) fn new(sem_env: &'tc SemEnv<'tc>) -> Self {
        Self { sem_env, bindings_by_name: HeavyState::new(Vec::new()) }
    }

    /// Find a binding by name, returning the symbol of the binding.
    ///
    /// This will search the current scope and all parent scopes.
    /// If the binding is not found, it will return `None`.
    ///
    /// Will panic if there are no scopes in the context.
    pub(super) fn get_current_context_kind(&self) -> ContextKind {
        self.bindings_by_name.get().last().unwrap().0
    }

    /// Find a binding by name, returning the symbol of the binding.
    ///
    /// This will search the current scope and all parent scopes.
    /// If the binding is not found, it will return `None`.
    fn lookup_symbol_by_name(&self, name: impl Into<Identifier>) -> Option<Symbol> {
        let name = name.into();
        let binding = match self.get_current_context_kind() {
            ContextKind::Access(_, _) => {
                // If we are accessing we only want to look in the current scope
                self.bindings_by_name.get().last().and_then(|binding| binding.1.get(&name).copied())
            }
            ContextKind::Environment => {
                // Look up the scopes
                self.bindings_by_name.get().iter().rev().find_map(|b| b.1.get(&name).copied())
            }
        }?;

        Some(binding)
    }

    /// Find a binding by name, returning the symbol of the binding.
    ///
    /// Errors if the binding is not found or used in the wrong context.
    ///
    /// See [`SymbolResolutionPass::lookup_binding_by_name()`].
    pub(super) fn lookup_symbol_by_name_or_error(
        &self,
        name: impl Into<Identifier>,
        span: Span,
        looking_in: ContextKind,
    ) -> SemanticResult<Symbol> {
        let name = name.into();
        let symbol =
            self.lookup_symbol_by_name(name).ok_or_else(|| SemanticError::SymbolNotFound {
                symbol: self.new_symbol(name),
                location: self.source_location(span),
                looking_in,
            })?;

        if self.context().get_current_scope().kind.is_constant() {
            // If we are in a constant scope, we need to check that the binding
            // is also in a constant scope.
            if !self.context().get_binding(symbol).kind.is_constant() {
                return Err(SemanticError::CannotUseNonConstantItem {
                    location: self.source_location(span),
                });
            }
        }

        Ok(symbol)
    }

    /// Run a function in a new scope, and then exit the scope.
    pub(super) fn enter_scope<T>(
        &self,
        kind: ScopeKind,
        context_kind: ContextKind,
        f: impl FnOnce() -> T,
    ) -> T {
        self.context().enter_scope(kind, || {
            self.bindings_by_name.enter(
                |b| {
                    b.push((context_kind, HashMap::new()));
                },
                |b| {
                    // Exit the scope on the context exit.
                    b.pop();
                },
                f,
            )
        })
    }

    /// Add a new scope
    pub(super) fn add_scope(&self, kind: ScopeKind, context_kind: ContextKind) {
        self.context().add_scope(kind);
        let mut b = self.bindings_by_name.get_mut();
        // Initialise the name map. Any duplicate names will be shadowed by the last
        // entry.
        b.push((context_kind, HashMap::new()));
    }

    /// Add a parameter to the current scope, also adding it to the
    /// `bindings_by_name` map.
    pub(super) fn add_param_binding(&self, param_id: ParamId, origin: ParamOrigin) {
        // Get the data of the parameter.
        let param_name = self.stores().params().get_element(param_id).name;

        // Add the binding to the current scope.
        self.context_utils().add_param_binding(param_id, origin);
        self.add_named_binding(param_name);
    }

    /// Add a stack member to the current scope, also adding it to the
    /// `bindings_by_name` map.
    pub(super) fn add_stack_binding(&self, member_id: StackMemberId, value: Option<TermId>) {
        // Get the data of the member.
        let member_name = self.get_stack_member_name(member_id);
        // Add the binding to the current scope.
        self.context_utils().add_stack_binding(member_id, value);
        self.add_named_binding(member_name);
    }

    /// Add the data parameters constructors of the definition to the current
    /// scope, also adding them to the `bindings_by_name` map.
    pub(super) fn add_data_params_and_ctors(&self, data_def_id: DataDefId) {
        let params = self.stores().data_def().map_fast(data_def_id, |def| def.params);
        for i in params.to_index_range() {
            self.add_param_binding((params, i), data_def_id.into());
        }
        self.context_utils()
            .add_data_ctors(data_def_id, |binding| self.add_named_binding(binding.name));
    }

    /// Add the module members of the definition to the current scope,
    /// also adding them to the `bindings_by_name` map.
    pub(super) fn add_mod_members(&self, mod_def_id: ModDefId) {
        self.context_utils()
            .add_mod_members(mod_def_id, |binding| self.add_named_binding(binding.name));
    }

    /// Add a named binding to the current scope, by recording its identifier
    /// name.
    fn add_named_binding(&self, name: Symbol) {
        let name_data = self.stores().symbol().get(name);

        // Add the binding to the `bindings_by_name` map.
        if let Some(ident_name) = name_data.name {
            match self.bindings_by_name.get_mut().last_mut() {
                Some(bindings) => {
                    bindings.1.insert(ident_name, name);
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
    pub(super) fn for_each_stack_member_of_pat(
        &self,
        node: ast::AstNodeRef<ast::Pat>,
        f: &mut impl FnMut(StackMemberId),
    ) {
        macro_rules! for_spread_pat {
            ($spread:expr) => {
                if let Some(name) = &$spread.name {
                    if let Some(member_id) =
                        self.ast_info().stack_members().get_data_by_node(name.ast_ref().id())
                    {
                        f(member_id);
                    }
                }
            };
        }

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
                        for_spread_pat!(spread_node);
                    }
                    self.for_each_stack_member_of_pat(entry.pat.ast_ref(), f);
                }
            }
            ast::Pat::Constructor(constructor_pat) => {
                for (index, field) in constructor_pat.fields.ast_ref_iter().enumerate() {
                    if let Some(spread_node) = &constructor_pat.spread && spread_node.position == index {
                        for_spread_pat!(spread_node);
                    }
                    self.for_each_stack_member_of_pat(field.pat.ast_ref(), f);
                }
            }
            ast::Pat::Array(array_pat) => {
                for (index, pat) in array_pat.fields.ast_ref_iter().enumerate() {
                    if let Some(spread_node) = &array_pat.spread && spread_node.position == index {
                        for_spread_pat!(spread_node);
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

    /// Enter the scope of a body block.
    ///
    /// If called on a non-stack body block, it will return none.
    pub(super) fn enter_body_block<T>(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
        f: impl FnOnce(StackId) -> T,
    ) -> Option<T> {
        self.ast_info().stacks().get_data_by_node(node.id()).map(|stack_id| {
            self.enter_scope(ScopeKind::Stack(stack_id), ContextKind::Environment, || f(stack_id))
        })
    }

    /// Enter the scope of a type function type
    pub(super) fn enter_ty_fn_ty<T>(
        &self,
        node: ast::AstNodeRef<ast::TyFn>,
        f: impl FnOnce(FnTy) -> T,
    ) -> T {
        let fn_ty_id = self.ast_info().tys().get_data_by_node(node.id()).unwrap();
        let fn_ty = ty_as_variant!(self, self.get_ty(fn_ty_id), Fn);
        self.enter_scope(ScopeKind::FnTy(fn_ty), ContextKind::Environment, || f(fn_ty))
    }

    /// Enter the scope of a function type
    pub(super) fn enter_fn_ty<T>(
        &self,
        node: ast::AstNodeRef<ast::FnTy>,
        f: impl FnOnce(FnTy) -> T,
    ) -> T {
        let fn_ty_id = self.ast_info().tys().get_data_by_node(node.id()).unwrap();
        let fn_ty = ty_as_variant!(self, self.get_ty(fn_ty_id), Fn);
        self.enter_scope(ScopeKind::FnTy(fn_ty), ContextKind::Environment, || f(fn_ty))
    }

    /// Enter the scope of a tuple type
    pub(super) fn enter_tuple_ty<T>(
        &self,
        node: ast::AstNodeRef<ast::TupleTy>,
        f: impl FnOnce(TupleTy) -> T,
    ) -> T {
        let tuple_ty_id = self.ast_info().tys().get_data_by_node(node.id()).unwrap();
        let tuple_ty = ty_as_variant!(self, self.get_ty(tuple_ty_id), Tuple);
        self.enter_scope(ScopeKind::TupleTy(tuple_ty), ContextKind::Environment, || f(tuple_ty))
    }

    /// Register a declaration, which will add it to the current stack scope.
    ///
    /// Returns the range of stack indices that were added.
    ///
    /// If the declaration is not in a stack scope, this is a no-op.
    pub(super) fn register_declaration(
        &self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> StackIndices {
        if let ScopeKind::Stack(_) = self.context().get_current_scope().kind {
            let mut start_end = StackIndices::Empty;
            self.for_each_stack_member_of_pat(node.pat.ast_ref(), &mut |member| {
                start_end.extend_with_index(member.1);
                self.add_stack_binding(member, None);
            });
            start_end
        } else {
            StackIndices::Empty
        }
    }

    /// Enter a match case, adding the bindings to the current stack scope.
    pub(super) fn enter_match_case<T>(
        &self,
        node: ast::AstNodeRef<ast::MatchCase>,
        f: impl FnOnce(StackId, StackIndices) -> T,
    ) -> T {
        let stack_id = self.ast_info().stacks().get_data_by_node(node.id()).unwrap();
        // Each match case has its own scope, so we need to enter it, and add all the
        // pattern bindings to the context.
        self.enter_scope(ScopeKind::Stack(stack_id), ContextKind::Environment, || {
            // We also want to keep track of the start and end of the pattern
            // binds in the stack, to pass to `f`.
            let mut start_end = StackIndices::Empty;
            self.for_each_stack_member_of_pat(node.pat.ast_ref(), &mut |member| {
                start_end.extend_with_index(member.1);
                self.add_stack_binding(member, None);
            });
            f(stack_id, start_end)
        })
    }
}
