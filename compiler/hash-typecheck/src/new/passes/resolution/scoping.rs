//! General helper functions for traversing scopes and adding bindings.
use std::{collections::HashMap, fmt};

use hash_ast::ast;
use hash_source::{identifier::Identifier, location::Span};
use hash_types::new::{
    environment::{context::ScopeKind, env::AccessToEnv},
    locations::LocationTarget,
    scopes::StackMemberId,
    symbols::Symbol,
};
use hash_utils::{
    state::HeavyState,
    store::{CloneStore, Store},
};

use super::paths::NonTerminalResolvedPathComponent;
use crate::{
    impl_access_to_tc_env,
    new::{
        diagnostics::error::{TcError, TcResult},
        environment::tc_env::{AccessToTcEnv, TcEnv, WithTcEnv},
        ops::{common::CommonOps, AccessToOps},
        passes::ast_utils::AstUtils,
    },
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

/// Contains helper functions for traversing scopes and adding bindings.
///
/// It uses [`hash_types::new::environment::context::Context`] and
/// [`crate::new::ops::context::ContextOps`] to enter scopes, but also
/// keeps track of identifier names so that names can be matched to the correct
/// symbols when creating `Var` terms.
pub(super) struct Scoping<'tc> {
    tc_env: &'tc TcEnv<'tc>,
    /// Stores a list of contexts we are in, mirroring `ContextStore` but with
    /// identifiers so that we can resolve them to symbols.
    ///
    /// Also keeps track of the kind of context we are in.
    bindings_by_name: HeavyState<Vec<(ContextKind, HashMap<Identifier, Symbol>)>>,
}

impl_access_to_tc_env!(Scoping<'tc>);

impl AstUtils for Scoping<'_> {}

impl<'tc> Scoping<'tc> {
    pub(super) fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        Self { tc_env, bindings_by_name: HeavyState::new(Vec::new()) }
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
    pub(super) fn lookup_symbol_by_name(&self, name: impl Into<Identifier>) -> Option<Symbol> {
        let name = name.into();
        match self.get_current_context_kind() {
            ContextKind::Access(_, _) => {
                // If we are accessing we only want to look in the current scope
                self.bindings_by_name.get().last().and_then(|binding| binding.1.get(&name).copied())
            }
            ContextKind::Environment => {
                // Look up the scopes
                self.bindings_by_name.get().iter().rev().find_map(|b| b.1.get(&name).copied())
            }
        }
    }

    /// Find a binding by name, returning the symbol of the binding.
    ///
    /// Errors if the binding is not found.
    ///
    /// See [`SymbolResolutionPass::lookup_binding_by_name()`].
    pub(super) fn lookup_symbol_by_name_or_error(
        &self,
        name: impl Into<Identifier>,
        span: Span,
        looking_in: ContextKind,
    ) -> TcResult<Symbol> {
        let name = name.into();
        self.lookup_symbol_by_name(name).ok_or_else(|| TcError::SymbolNotFound {
            symbol: self.new_symbol(name),
            location: self.source_location(span),
            looking_in,
        })
    }

    /// Run a function in a new scope, and then exit the scope.
    ///
    /// In addition to adding the appropriate bindings, this also adds the
    /// appropriate names to `bindings_by_name`.
    pub(super) fn enter_scope<T>(
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
    pub(super) fn add_stack_binding(&self, member_id: StackMemberId) {
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
    pub(super) fn for_each_stack_member_of_pat(
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

    pub(super) fn _enter_module<T>(&self, _node: ast::AstNodeRef<ast::Module>) -> TcResult<T> {
        todo!()
    }
}
