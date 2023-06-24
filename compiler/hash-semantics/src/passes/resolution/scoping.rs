//! General helper functions for traversing scopes and adding bindings.
use std::{collections::HashMap, fmt};

use hash_ast::ast;
use hash_source::{identifier::Identifier, location::Span};
use hash_tir::{
    data::{CtorDefId, DataDefCtors, DataDefId},
    environment::{
        context::{ParamOrigin, ScopeKind},
        env::{AccessToEnv, Env},
    },
    fns::FnTy,
    locations::LocationTarget,
    mods::{ModDefId, ModMemberId},
    params::ParamId,
    scopes::StackId,
    symbols::Symbol,
    tuples::TupleTy,
    ty_as_variant,
    utils::common::CommonUtils,
};
use hash_utils::{
    state::HeavyState,
    store::{CloneStore, SequenceStore, SequenceStoreKey, Store},
};

use super::paths::NonTerminalResolvedPathComponent;
use crate::{
    diagnostics::error::{SemanticError, SemanticResult},
    environment::sem_env::{AccessToSemEnv, SemEnv, WithSemEnv},
    ops::common::CommonOps,
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
/// The kind of a binding.
#[derive(Debug, Clone, Copy)]
pub enum BindingKind {
    /// A binding that is a module member.
    ///
    /// For example, `mod { Q := struct(); Q }`
    ModMember(ModDefId, ModMemberId),
    /// A binding that is a constructor definition.
    ///
    /// For example, `false`, `None`, `Some(_)`.
    Ctor(DataDefId, CtorDefId),
    /// A symbolic binding.
    Sym(Symbol),
}

pub type Binding = (Symbol, BindingKind);

/// Contains helper functions for traversing scopes and adding bindings.
///
/// It uses [`hash_tir::environment::context::Context`] and
/// [`crate::ops::context::ContextOps`] to enter scopes, but also
/// keeps track of identifier names so that names can be matched to the correct
/// symbols when creating `Var` terms.
pub(super) struct Scoping<'tc> {
    sem_env: &'tc SemEnv<'tc>,
    /// Stores a list of contexts we are in, mirroring `ContextStore` but with
    /// identifiers so that we can resolve them to bindings.
    ///
    /// Also keeps track of the kind of context we are in.
    bindings_by_name: HeavyState<Vec<(ContextKind, HashMap<Identifier, Binding>)>>,
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
    fn lookup_symbol_by_name(&self, name: impl Into<Identifier>) -> Option<(Symbol, BindingKind)> {
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
    ) -> SemanticResult<(Symbol, BindingKind)> {
        let name = name.into();
        let symbol =
            self.lookup_symbol_by_name(name).ok_or_else(|| SemanticError::SymbolNotFound {
                symbol: self.new_symbol(name),
                location: self.source_location(span),
                looking_in,
            })?;

        // @@Todo: Ensure that we are in the correct context for the binding.
        // if self.context().get_current_scope_kind().is_constant() {
        //     // If we are in a constant scope, we need to check that the binding
        //     // is also in a constant scope.
        //     if !self.context().get_binding(symbol).kind.is_constant() {
        //         return Err(SemanticError::CannotUseNonConstantItem {
        //             location: self.source_location(span),
        //         });
        //     }
        // }

        Ok(symbol)
    }

    /// Run a function in a new scope, and then exit the scope.
    pub(super) fn enter_scope<T>(&self, context_kind: ContextKind, f: impl FnOnce() -> T) -> T {
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
    }

    /// Add a new scope
    pub(super) fn add_scope(&self, _kind: ScopeKind, context_kind: ContextKind) {
        // self.context().add_scope(kind);
        let mut b = self.bindings_by_name.get_mut();
        // Initialise the name map. Any duplicate names will be shadowed by the last
        // entry.
        b.push((context_kind, HashMap::new()));
    }

    /// Add a parameter to the current scope, also adding it to the
    /// `bindings_by_name` map.
    pub(super) fn add_param_binding(&self, param_id: ParamId, _origin: ParamOrigin) {
        // Get the data of the parameter.
        let param_name = self.stores().params().get_element(param_id).name;

        // Add the binding to the current scope.
        self.add_named_binding(param_name, BindingKind::Sym(param_name));
    }

    /// Add a stack member to the current scope, also adding it to the
    /// `bindings_by_name` map.
    pub(super) fn add_stack_binding(&self, name: Symbol) {
        // Add the binding to the current scope.
        self.add_named_binding(name, BindingKind::Sym(name));
    }

    /// Add the data parameters constructors of the definition to the current
    /// scope, also adding them to the `bindings_by_name` map.
    pub(super) fn add_data_params_and_ctors(&self, data_def_id: DataDefId) {
        let params = self.stores().data_def().map_fast(data_def_id, |def| def.params);
        for i in params.to_index_range() {
            self.add_param_binding((params, i), data_def_id.into());
        }
        self.stores().data_def().map_fast(data_def_id, |data_def| {
            // Add all the constructors
            match data_def.ctors {
                DataDefCtors::Defined(ctors) => {
                    self.stores().ctor_defs().map_fast(ctors, |ctors| {
                        for ctor in ctors.iter() {
                            self.add_named_binding(
                                ctor.name,
                                BindingKind::Ctor(data_def_id, ctor.id),
                            );
                        }
                    })
                }
                DataDefCtors::Primitive(_) => {
                    // No-op
                }
            }
        })
    }

    /// Add the module members of the definition to the current scope,
    /// also adding them to the `bindings_by_name` map.
    pub(super) fn add_mod_members(&self, mod_def_id: ModDefId) {
        self.stores().mod_def().map_fast(mod_def_id, |mod_def| {
            self.stores().mod_members().map_fast(mod_def.members, |members| {
                for member in members.iter() {
                    self.add_named_binding(
                        member.name,
                        BindingKind::ModMember(mod_def_id, member.id),
                    );
                }
            })
        })
    }

    /// Add a named binding to the current scope, by recording its identifier
    /// name.
    fn add_named_binding(&self, name: Symbol, kind: BindingKind) {
        let name_data = self.stores().symbol().get(name);

        // Add the binding to the `bindings_by_name` map.
        if let Some(ident_name) = name_data.name {
            match self.bindings_by_name.get_mut().last_mut() {
                Some(bindings) => {
                    bindings.1.insert(ident_name, (name, kind));
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
        f: &mut impl FnMut(Symbol),
    ) {
        macro_rules! for_spread_pat {
            ($spread:expr) => {
                if let Some(name) = &$spread.name {
                    if let Some(member_id) =
                        self.ast_info().stack_members().get_data_by_node(name.ast_ref().id())
                    {
                        f(member_id.name);
                    }
                }
            };
        }

        match node.body() {
            ast::Pat::Binding(_) => {
                if let Some(member_id) = self.ast_info().stack_members().get_data_by_node(node.id())
                {
                    f(member_id.name);
                }
            }
            ast::Pat::Tuple(tuple_pat) => {
                if let Some(spread_node) = &tuple_pat.spread {
                    for_spread_pat!(spread_node);
                }
                for entry in tuple_pat.fields.ast_ref_iter() {
                    self.for_each_stack_member_of_pat(entry.pat.ast_ref(), f);
                }
            }
            ast::Pat::Constructor(constructor_pat) => {
                if let Some(spread_node) = &constructor_pat.spread {
                    for_spread_pat!(spread_node);
                }
                for field in constructor_pat.fields.ast_ref_iter() {
                    self.for_each_stack_member_of_pat(field.pat.ast_ref(), f);
                }
            }
            ast::Pat::Array(array_pat) => {
                if let Some(spread_node) = &array_pat.spread {
                    for_spread_pat!(spread_node);
                }
                for pat in array_pat.fields.ast_ref_iter() {
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
                    f(member_id.name);
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
        self.ast_info()
            .stacks()
            .get_data_by_node(node.id())
            .map(|stack_id| self.enter_scope(ContextKind::Environment, || f(stack_id)))
    }

    /// Enter the scope of a type function type
    pub(super) fn enter_ty_fn_ty<T>(
        &self,
        node: ast::AstNodeRef<ast::TyFn>,
        f: impl FnOnce(FnTy) -> T,
    ) -> T {
        let fn_ty_id = self.ast_info().tys().get_data_by_node(node.id()).unwrap();
        let fn_ty = ty_as_variant!(self, self.get_ty(fn_ty_id), Fn);
        self.enter_scope(ContextKind::Environment, || f(fn_ty))
    }

    /// Enter the scope of a function type
    pub(super) fn enter_fn_ty<T>(
        &self,
        node: ast::AstNodeRef<ast::FnTy>,
        f: impl FnOnce(FnTy) -> T,
    ) -> T {
        let fn_ty_id = self.ast_info().tys().get_data_by_node(node.id()).unwrap();
        let fn_ty = ty_as_variant!(self, self.get_ty(fn_ty_id), Fn);
        self.enter_scope(ContextKind::Environment, || f(fn_ty))
    }

    /// Enter the scope of a tuple type
    pub(super) fn enter_tuple_ty<T>(
        &self,
        node: ast::AstNodeRef<ast::TupleTy>,
        f: impl FnOnce(TupleTy) -> T,
    ) -> T {
        let tuple_ty_id = self.ast_info().tys().get_data_by_node(node.id()).unwrap();
        let tuple_ty = ty_as_variant!(self, self.get_ty(tuple_ty_id), Tuple);
        self.enter_scope(ContextKind::Environment, || f(tuple_ty))
    }

    /// Register a declaration, which will add it to the current stack scope.
    ///
    /// Returns the range of stack indices that were added.
    ///
    /// If the declaration is not in a stack scope, this is a no-op.
    pub(super) fn register_declaration(&self, node: ast::AstNodeRef<ast::Declaration>) {
        self.for_each_stack_member_of_pat(node.pat.ast_ref(), &mut |member| {
            self.add_stack_binding(member);
        });
    }

    /// Enter a match case, adding the bindings to the current stack scope.
    pub(super) fn enter_match_case<T>(
        &self,
        node: ast::AstNodeRef<ast::MatchCase>,
        f: impl FnOnce(StackId) -> T,
    ) -> T {
        let stack_id = self.ast_info().stacks().get_data_by_node(node.id()).unwrap();
        // Each match case has its own scope, so we need to enter it, and add all the
        // pattern bindings to the context.
        self.enter_scope(ContextKind::Environment, || {
            self.for_each_stack_member_of_pat(node.pat.ast_ref(), &mut |member| {
                self.add_stack_binding(member);
            });
            f(stack_id)
        })
    }
}
