use std::collections::HashMap;

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
    args::{ArgData, ArgsId},
    data::{CtorTerm, DataDefId, DataTy},
    defs::{DefArgGroupData, DefArgsId, DefParamsId},
    environment::{
        context::{Binding, BindingKind, ScopeKind},
        env::AccessToEnv,
    },
    fns::FnCallTerm,
    mods::{ModDefId, ModMemberValue},
    params::ParamTarget,
    scopes::{BoundVar, StackMemberId},
    symbols::Symbol,
    terms::{Term, TermId},
    tys::{Ty, TyId},
};
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey, Store};

use super::{
    ast_pass::AstPass,
    state::{HeavyState, LightState},
};
use crate::{
    impl_access_to_tc_env,
    new::{
        diagnostics::{
            error::{TcError, TcResult},
            params::{SomeArgsId, SomeDefArgsId},
        },
        environment::tc_env::{AccessToTcEnv, TcEnv},
        ops::{ast::AstOps, common::CommonOps, AccessToOps},
    },
};

/// The current expression kind we are in.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InExpr {
    /// We are in a type expression.
    Ty,
    /// We are in a value expression.
    Value,
}

/// The second pass of the typechecker, which resolves all symbols to their
/// referenced bindings.
pub struct SymbolResolutionPass<'tc> {
    tc_env: &'tc TcEnv<'tc>,
    in_expr: LightState<InExpr>,
    bindings_by_name: HeavyState<Vec<HashMap<Identifier, Symbol>>>,
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
    fn lookup_binding_by_name(&self, name: Identifier) -> Option<Symbol> {
        self.bindings_by_name.get().iter().rev().find_map(|b| b.get(&name).copied())
    }

    /// Find a binding by name, returning the symbol of the binding.
    ///
    /// Errors if the binding is not found.
    ///
    /// See [`SymbolResolutionPass::lookup_binding_by_name()`].
    fn lookup_binding_by_name_or_error(&self, name: Identifier, span: Span) -> TcResult<Symbol> {
        self.lookup_binding_by_name(name).ok_or_else(|| TcError::SymbolNotFound {
            symbol: self.new_symbol(name),
            location: self.source_location(span),
        })
    }

    /// Run a function in a new scope, and then exit the scope.
    ///
    /// In addition to adding the appropriate bindings, this also adds the
    /// appropriate names to `bindings_by_name`.
    fn enter_scope<T>(&self, kind: ScopeKind, f: impl FnOnce() -> T) -> T {
        self.context_ops().enter_scope(kind, || {
            self.bindings_by_name.enter(
                |b| {
                    let current_level = self.context().get_current_scope_level();

                    // Populate the map with all the bindings in the current
                    // scope. Any duplicate names will be shadowed by the last entry.
                    // @@Semantics: Should we report an error if there are duplicate names?
                    let mut map = HashMap::new();
                    self.context().for_bindings_of_level(current_level, |binding| {
                        let symbol_data = self.stores().symbol().get(binding.name);
                        if let Some(name) = symbol_data.name {
                            map.insert(name, binding.name);
                        }
                    });

                    b.push(map);
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
                    bindings.insert(name, member_name);
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

/// An argument group in the AST.
///
/// This is either a group of explicit `(a, b, c)` arguments, or a group of
/// implicit `<a, b, c>` arguments. The former corresponds to the
/// [`ast::ConstructorCallArg`], while the latter corresponds to the
/// [`ast::TyArg`].
#[derive(Copy, Clone, Debug)]
#[allow(dead_code)]
enum AstArgGroup<'a> {
    /// A group of explicit `(a, b, c)` arguments.
    ExplicitArgs(&'a ast::AstNodes<ast::ConstructorCallArg>),
    /// A group of implicit `<a, b, c>` arguments.
    ImplicitArgs(&'a ast::AstNodes<ast::TyArg>),
}

impl AstArgGroup<'_> {
    /// Get the span of this argument group.
    pub(self) fn span(&self) -> Option<Span> {
        match self {
            AstArgGroup::ExplicitArgs(args) => args.span(),
            AstArgGroup::ImplicitArgs(args) => args.span(),
        }
    }
}

/// A path component in the AST.
///
/// A path is a sequence of path components, separated by `::`.
/// A path component is either a name, or a name followed by a list of
/// argument groups, each of which is a [`AstArgGroup`].
///
/// For example: `Foo::Bar::Baz<T, U>(a, b, c)::Bin(3)`.
#[derive(Clone, Debug)]
struct AstPathComponent<'a> {
    pub(self) name: &'a ast::AstNode<ast::Name>,
    pub(self) args: Vec<AstArgGroup<'a>>,
}

/// A path in the AST.
///
/// For example, `Foo::Bar`.
type AstPath<'a> = Vec<AstPathComponent<'a>>;

impl AstPathComponent<'_> {
    /// Get the span of this path component.
    pub(self) fn span(&self) -> Span {
        self.name.span().join(self.args.iter().fold(self.name.span(), |acc, arg| {
            arg.span().map(|s| acc.join(s)).unwrap_or(self.name.span())
        }))
    }
}

/// The result of resolving a path component.
///
/// This is either a [`ModMemberValue`], which can
/// support further access, or a [`TermId`], which
/// is a terminal value.
#[derive(Clone, Copy, Debug)]
enum ResolvedAstPathComponent {
    Data(DataDefId, DefArgsId),
    Mod(ModDefId, DefArgsId),
    Term(TermId),
    Ty(TyId),
}

/// The result of resolving a path.
///
/// This is either a [`TermId`], or a [`TyId`].
#[derive(Clone, Copy, Debug)]
enum ResolvedAstPath {
    Term(TermId),
    Ty(TyId),
}

/// This block performs resolution of AST paths.
impl<'tc> SymbolResolutionPass<'tc> {
    /// Resolve a name starting from the given [`ModMemberValue`], or the
    /// current context if no such value is given.
    ///
    /// Returns the binding that the name resolves to.
    fn resolve_ast_name(
        &self,
        name: AstNodeRef<ast::Name>,
        starting_from: Option<(ModMemberValue, Span)>,
    ) -> TcResult<Binding> {
        let var_name = name.ident;

        match starting_from {
            Some((member_value, span)) => match member_value {
                // If we are starting from a module or data type, we need to enter their scopes.
                ModMemberValue::Data(data_def_id) => self
                    .enter_scope(ScopeKind::Data(data_def_id), || {
                        self.resolve_ast_name(name, None)
                    }),
                ModMemberValue::Mod(mod_def_id) => self
                    .enter_scope(ScopeKind::Mod(mod_def_id), || self.resolve_ast_name(name, None)),
                // Cannot use a function as a namespace.
                ModMemberValue::Fn(_) => {
                    Err(TcError::InvalidNamespaceSubject { location: self.source_location(span) })
                }
            },
            None => {
                // If there is no start point, try to lookup the variable in the current scope.
                let binding_symbol = self.lookup_binding_by_name_or_error(var_name, name.span())?;
                Ok(self.context().get_binding(binding_symbol).unwrap())
            }
        }
    }

    /// Make [`ArgsId`] from an AST argument group, with holes for all the
    /// arguments.
    fn make_args_from_ast_arg_group(&self, group: &AstArgGroup) -> ArgsId {
        macro_rules! make_args_from_ast_args {
            ($args:expr) => {
                self.param_ops().create_args($args.iter().enumerate().map(|(i, arg)| {
                    return ArgData {
                        target: arg
                            .name
                            .as_ref()
                            .map(|name| ParamTarget::Name(name.ident))
                            .unwrap_or_else(|| ParamTarget::Position(i)),
                        value: self.new_term_hole(),
                    };
                }))
            };
        }
        match group {
            AstArgGroup::ExplicitArgs(args) => make_args_from_ast_args!(args),
            AstArgGroup::ImplicitArgs(args) => make_args_from_ast_args!(args),
        }
    }

    /// Make [`DefArgsId`] from a list of AST argument groups, using
    /// `make_args_from_ast_arg_group` to make each argument group.
    fn make_def_args_from_ast_arg_groups(
        &self,
        groups: &[AstArgGroup],
        originating_params: DefParamsId,
    ) -> DefArgsId {
        self.param_ops().create_def_args(groups.iter().enumerate().map(|(index, group)| {
            DefArgGroupData {
                args: self.make_args_from_ast_arg_group(group),
                param_group: (originating_params, index),
            }
        }))
    }

    /// Wrap a term in a function call, given a list of arguments as a list of
    /// [`AstArgGroup`].
    ///
    /// Creates a new [`TermId`], which is a term that represents the
    /// function call, and might be nested depending on `args`.
    fn wrap_term_in_fn_call_from_ast_args(&self, subject: TermId, args: &[AstArgGroup]) -> TermId {
        let mut current_subject = subject;
        for arg_group in args {
            let args = self.make_args_from_ast_arg_group(arg_group);
            current_subject = self.new_term(Term::FnCall(FnCallTerm {
                subject: current_subject,
                args,
                implicit: matches!(arg_group, AstArgGroup::ImplicitArgs(_)),
            }));
        }
        current_subject
    }

    /// Apply the given list of AST arguments to the given definition
    /// parameters, checking that the lengths match in the process.
    ///
    /// If successful, returns the [`DefArgsId`] that represents the arguments.
    ///
    /// Otherwise, returns an error.
    fn apply_ast_args_to_def_params(
        &self,
        def_params: DefParamsId,
        args: &[AstArgGroup],
    ) -> TcResult<DefArgsId> {
        // @@Todo: implicit args

        // First ensure that the number of parameter and argument groups match.
        let created_def_args = self.make_def_args_from_ast_arg_groups(args, def_params);
        if def_params.len() != created_def_args.len() {
            return Err(TcError::WrongDefArgLength {
                def_params_id: def_params,
                def_args_id: SomeDefArgsId::Args(created_def_args),
            });
        }

        // Then ensure that the number of parameters and arguments in each group
        // match.
        let mut errors: Vec<TcError> = vec![];
        for (param_group_index, arg_group_index) in
            def_params.to_index_range().zip(created_def_args.to_index_range())
        {
            let def_param_group =
                self.stores().def_params().get_element((def_params, param_group_index));
            let def_arg_group =
                self.stores().def_args().get_element((created_def_args, arg_group_index));

            if def_param_group.params.len() != def_arg_group.args.len() {
                // Collect errors and only report at the end.
                errors.push(TcError::WrongArgLength {
                    params_id: def_param_group.params,
                    args_id: SomeArgsId::Args(def_arg_group.args),
                });
            }
        }
        if !errors.is_empty() {
            return Err(TcError::Compound { errors });
        }

        Ok(created_def_args)
    }

    /// Resolve a path component, starting from the given [`ModMemberValue`] if
    /// present, or the current context if not. Also takes into account if
    /// we are in a type or value context.
    ///
    /// The `total_span` argument is the span of the entire path, and is used
    /// for error reporting.
    ///
    /// Returns a [`ResolvedAstPathComponent`] which might or might not support
    /// further accessing.
    ///
    /// Invariants:
    /// - `in_expr == InExpr::Value` returns either a term or a mod member
    /// - `in_expr == InExpr::Ty` returns either a type or a mod member
    fn resolve_ast_path_component(
        &self,
        component: &AstPathComponent<'_>,
        starting_from: Option<(ModMemberValue, Span)>,
        in_expr: InExpr,
        total_span: Span,
    ) -> TcResult<ResolvedAstPathComponent> {
        let binding = self.resolve_ast_name(component.name.ast_ref(), starting_from)?;

        match binding.kind {
            BindingKind::ModMember(_, mod_member_id) => {
                let mod_member = self.stores().mod_members().get_element(mod_member_id);
                match mod_member.value {
                    ModMemberValue::Data(data_def_id) => {
                        let data_def_params =
                            self.stores().data_def().map_fast(data_def_id, |def| def.params);
                        let args =
                            self.apply_ast_args_to_def_params(data_def_params, &component.args)?;
                        Ok(ResolvedAstPathComponent::Data(data_def_id, args))
                    }
                    ModMemberValue::Mod(mod_def_id) => {
                        let mod_def_params =
                            self.stores().mod_def().map_fast(mod_def_id, |def| def.params);
                        let args =
                            self.apply_ast_args_to_def_params(mod_def_params, &component.args)?;
                        Ok(ResolvedAstPathComponent::Mod(mod_def_id, args))
                    }
                    ModMemberValue::Fn(fn_def_id) => {
                        // If a function is used in a value position, then it is
                        // the function's address that is used.
                        if in_expr == InExpr::Ty {
                            return Err(TcError::CannotUseFunctionInTypePosition {
                                location: self.source_location(total_span),
                            });
                        }

                        // Apply any arguments to the function.
                        let resultant_term = self.wrap_term_in_fn_call_from_ast_args(
                            self.new_term(Term::FnRef(fn_def_id)),
                            &component.args,
                        );

                        // Return a term or a type as appropriate by `in_expr`.
                        match in_expr {
                            InExpr::Ty => Ok(ResolvedAstPathComponent::Ty(
                                self.new_ty(Ty::Eval(resultant_term)),
                            )),
                            InExpr::Value => Ok(ResolvedAstPathComponent::Term(resultant_term)),
                        }
                    }
                }
            }
            BindingKind::Ctor(_, ctor_def_id) => {
                // A constructor cannot be namespaced further, so it becomes
                // a term.
                if in_expr == InExpr::Ty {
                    // @@Improvement: support shorthand refinement like `None` as `Option<T> of
                    // None`.
                    return Err(TcError::CannotUseConstructorInTypePosition {
                        location: self.source_location(total_span),
                    });
                }

                let ctor_def = self.stores().ctor_defs().get_element(ctor_def_id);

                // Apply the arguments to the constructor.
                let args = self.apply_ast_args_to_def_params(ctor_def.params, &component.args)?;

                // Create a constructor term.
                Ok(ResolvedAstPathComponent::Term(
                    self.new_term(Term::Ctor(CtorTerm { ctor: ctor_def_id, args })),
                ))
            }
            BindingKind::BoundVar(bound_var) => {
                // If the subject without args is a bound variable, then the
                // rest are function arguments, and it becomes a term.
                let resultant_term = self.wrap_term_in_fn_call_from_ast_args(
                    self.new_term(Term::Var(BoundVar { name: binding.name, origin: bound_var })),
                    &component.args,
                );

                // Return a term or a type as appropriate by `in_expr`.
                match in_expr {
                    InExpr::Ty => {
                        Ok(ResolvedAstPathComponent::Ty(self.new_ty(Ty::Eval(resultant_term))))
                    }
                    InExpr::Value => Ok(ResolvedAstPathComponent::Term(resultant_term)),
                }
            }
        }
    }

    /// Resolve a path in the current context, returning either a term or a type
    /// as appropriate.
    ///
    /// Invariants:
    /// - `in_expr == InExpr::Value` returns a term
    /// - `in_expr == InExpr::Ty` returns a type
    fn resolve_ast_path<T>(
        &self,
        path: &AstPath,
        in_expr: InExpr,
        original_node: AstNodeRef<T>,
    ) -> TcResult<ResolvedAstPath> {
        assert!(!path.is_empty());

        let mut resolved_path =
            self.resolve_ast_path_component(&path[0], None, in_expr, original_node.span())?;

        for (index, component) in path.iter().enumerate().skip(1) {
            // For each component, we need to resolve it, and then namespace
            // further if possible.
            match resolved_path {
                ResolvedAstPathComponent::Mod(mod_def_id, _) => {
                    // Namespace further if it is a mod member.
                    resolved_path = self.resolve_ast_path_component(
                        component,
                        Some((ModMemberValue::Mod(mod_def_id), component.span())),
                        in_expr,
                        original_node.span(),
                    )?;
                }
                ResolvedAstPathComponent::Data(data_def_id, _) => {
                    // Namespace further if it is a data member.
                    resolved_path = self.resolve_ast_path_component(
                        component,
                        Some((ModMemberValue::Data(data_def_id), component.span())),
                        in_expr,
                        original_node.span(),
                    )?;
                }
                ResolvedAstPathComponent::Term(_) | ResolvedAstPathComponent::Ty(_) => {
                    // Cannot namespace further if it is a term or a type.
                    return Err(TcError::InvalidNamespaceSubject {
                        location: self.source_location(
                            path[..index]
                                .iter()
                                .map(|c| c.span())
                                .reduce(|a, b| a.join(b))
                                .unwrap(),
                        ),
                    });
                }
            }
        }

        // Now we inspect the resultant resolved value and make sure it is compatible in
        // the original context:
        match resolved_path {
            ResolvedAstPathComponent::Data(data_def_id, args_id) => {
                match in_expr {
                    InExpr::Ty => {
                        // If we are in a type position, then we need to wrap the data in a
                        // `Ty::Data` type.
                        Ok(ResolvedAstPath::Ty(
                            self.new_ty(Ty::Data(DataTy { data_def: data_def_id, args: args_id })),
                        ))
                    }
                    InExpr::Value => {
                        // If we are in a value position, then it is not valid to use `Data`.
                        // @@Todo: structs
                        Err(TcError::CannotUseDataTypeInValuePosition {
                            location: self.node_location(original_node),
                        })
                    }
                }
            }
            ResolvedAstPathComponent::Mod(_, _) => {
                // This is never valid, so we just return the appropriate error.
                match in_expr {
                    InExpr::Ty => Err(TcError::CannotUseModuleInValuePosition {
                        location: self.node_location(original_node),
                    }),
                    InExpr::Value => Err(TcError::CannotUseModuleInTypePosition {
                        location: self.node_location(original_node),
                    }),
                }
            }
            ResolvedAstPathComponent::Term(term_id) => {
                assert!(in_expr == InExpr::Value);
                Ok(ResolvedAstPath::Term(term_id))
            }
            ResolvedAstPathComponent::Ty(ty_id) => {
                assert!(in_expr == InExpr::Ty);
                Ok(ResolvedAstPath::Ty(ty_id))
            }
        }
    }

    /// Resolve a path in the current context, and add the result to the node.
    ///
    /// If there is an error, add it to the diagnostics.
    fn resolve_ast_path_and_add_to_node<T: std::fmt::Debug>(
        &self,
        path: &AstPath,
        original_node: AstNodeRef<T>,
    ) {
        match self.resolve_ast_path(path, self.in_expr.get(), original_node) {
            Ok(resolved) => match resolved {
                ResolvedAstPath::Term(term_id) => {
                    println!("Resolved term: {:?} -> {}", original_node, self.env().with(term_id));
                    self.ast_info().terms().insert(original_node.id(), term_id);
                }
                ResolvedAstPath::Ty(ty_id) => {
                    println!("Resolved type: {:?} -> {}", original_node, self.env().with(ty_id));
                    self.ast_info().tys().insert(original_node.id(), ty_id);
                }
            },
            Err(err) => {
                self.diagnostics().add_error(err);
            }
        }
    }
}

/// This block converts AST nodes of different kinds into [`AstPath`]s, in order
/// to later resolve them into terms.
impl<'tc> SymbolResolutionPass<'tc> {
    /// Use the given [`ast::VariableExpr`] as a path.
    fn variable_expr_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::VariableExpr>,
    ) -> TcResult<AstPath<'a>> {
        Ok(vec![AstPathComponent { name: &node.body.name, args: vec![] }])
    }

    /// Use the given [`ast::NamedTy`] as a path.
    fn named_ty_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::NamedTy>,
    ) -> TcResult<AstPath<'a>> {
        Ok(vec![AstPathComponent { name: &node.body.name, args: vec![] }])
    }

    /// Use the given [`ast::AccessTy`] as a path.
    fn access_ty_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::AccessTy>,
    ) -> TcResult<AstPath<'a>> {
        let mut root = self.ty_as_ast_path(node.body.subject.ast_ref())?;
        root.push(AstPathComponent { name: &node.body.property, args: vec![] });
        Ok(root)
    }

    /// Use the given [`ast::AccessExpr`] as a path.
    fn access_expr_as_ast_path<'a>(
        &self,
        _node: AstNodeRef<'a, ast::AccessExpr>,
    ) -> TcResult<AstPath<'a>> {
        todo!()
    }

    /// Use the given [`ast::Expr`] as a path, if possible.
    ///
    /// Returns an error if the expression is not a path. This is meant to
    /// be called from other `with_*_as_ast_path` functions.
    fn expr_as_ast_path<'a>(&self, _node: AstNodeRef<'a, ast::Expr>) -> TcResult<AstPath<'a>> {
        todo!()
    }

    /// Use the given [`ast::Ty`] as a path, if possible.
    ///
    /// Returns an error if the expression is not a path. This is meant to
    /// be called from other `with_*_as_ast_path` functions.
    fn ty_as_ast_path<'a>(&self, node: AstNodeRef<'a, ast::Ty>) -> TcResult<AstPath<'a>> {
        match node.body {
            ast::Ty::Access(access_ty) => {
                let access_ref = node.with_body(access_ty);
                self.access_ty_as_ast_path(access_ref)
            }
            ast::Ty::Named(named_ty) => {
                let named_ref = node.with_body(named_ty);
                self.named_ty_as_ast_path(named_ref)
            }
            ast::Ty::TyFnCall(ty_fn_call) => {
                let ty_fn_call_ref = node.with_body(ty_fn_call.subject.body());
                let mut path = self.expr_as_ast_path(ty_fn_call_ref)?;
                match path.pop() {
                    Some(mut component) => {
                        component.args.push(AstArgGroup::ImplicitArgs(&ty_fn_call.args));
                        path.push(AstPathComponent { name: component.name, args: component.args });
                        Ok(path)
                    }
                    None => panic!("Expected at least one path component"),
                }
            }
            ast::Ty::Tuple(_)
            | ast::Ty::List(_)
            | ast::Ty::Set(_)
            | ast::Ty::Map(_)
            | ast::Ty::Fn(_)
            | ast::Ty::Ref(_)
            | ast::Ty::Merge(_)
            | ast::Ty::Union(_)
            | ast::Ty::TyFn(_) => {
                Err(TcError::InvalidNamespaceSubject { location: self.node_location(node) })
            }
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
        Ty,
        VariableExpr,
        AccessExpr,
        AccessPat,
        ConstructorPat,
        AccessTy,
        NamedTy,
    );

    type ModuleRet = ();
    fn visit_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Mod(mod_def_id), || walk::walk_module(self, node))?;
        Ok(())
    }

    type ModDefRet = ();
    fn visit_mod_def(
        &self,
        node: ast::AstNodeRef<ast::ModDef>,
    ) -> Result<Self::ModDefRet, Self::Error> {
        let mod_def_id = self.ast_info().mod_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Mod(mod_def_id), || walk::walk_mod_def(self, node))?;
        Ok(())
    }

    type StructDefRet = ();
    fn visit_struct_def(
        &self,
        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let data_def_id = self.ast_info().data_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Data(data_def_id), || walk::walk_struct_def(self, node))?;
        Ok(())
    }

    type EnumDefRet = ();
    fn visit_enum_def(
        &self,
        node: ast::AstNodeRef<ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let data_def_id = self.ast_info().data_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Data(data_def_id), || walk::walk_enum_def(self, node))?;
        Ok(())
    }

    type FnDefRet = ();
    fn visit_fn_def(
        &self,
        node: ast::AstNodeRef<ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        let fn_def_id = self.ast_info().fn_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Fn(fn_def_id), || walk::walk_fn_def(self, node))?;
        Ok(())
    }

    type TyFnDefRet = ();
    fn visit_ty_fn_def(
        &self,
        node: ast::AstNodeRef<ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let fn_def_id = self.ast_info().fn_defs().get_data_by_node(node.id()).unwrap();
        self.enter_scope(ScopeKind::Fn(fn_def_id), || walk::walk_ty_fn_def(self, node))?;
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
                self.enter_scope(ScopeKind::Stack(stack_id), || {
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
        self.enter_scope(ScopeKind::Stack(stack_id), || {
            self.for_each_stack_member_of_pat(node.pat.ast_ref(), |member| {
                self.add_stack_binding(member);
            });
            walk::walk_match_case(self, node)?;
            Ok(())
        })
    }

    type TyRet = ();
    fn visit_ty(&self, node: ast::AstNodeRef<ast::Ty>) -> Result<Self::TyRet, Self::Error> {
        self.in_expr.enter(InExpr::Ty, || walk::walk_ty(self, node))?;
        Ok(())
    }

    type ExprRet = ();
    fn visit_expr(&self, node: ast::AstNodeRef<ast::Expr>) -> Result<Self::ExprRet, Self::Error> {
        self.in_expr.enter(InExpr::Value, || walk::walk_expr(self, node))?;
        Ok(())
    }

    type VariableExprRet = ();
    fn visit_variable_expr(
        &self,
        node: ast::AstNodeRef<ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        let path = self.variable_expr_as_ast_path(node)?;
        self.resolve_ast_path_and_add_to_node(&path, node);
        Ok(())
    }

    type NamedTyRet = ();
    fn visit_named_ty(
        &self,
        node: ast::AstNodeRef<ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        let path = self.named_ty_as_ast_path(node)?;
        self.resolve_ast_path_and_add_to_node(&path, node);
        Ok(())
    }

    type AccessTyRet = ();
    fn visit_access_ty(
        &self,
        node: ast::AstNodeRef<ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        let path = self.access_ty_as_ast_path(node)?;
        self.resolve_ast_path_and_add_to_node(&path, node);
        Ok(())
    }

    type AccessPatRet = ();
    fn visit_access_pat(
        &self,
        _node: ast::AstNodeRef<ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        Ok(())
    }

    type AccessExprRet = ();
    fn visit_access_expr(
        &self,
        node: ast::AstNodeRef<ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        let path = self.access_expr_as_ast_path(node)?;
        self.resolve_ast_path_and_add_to_node(&path, node);
        Ok(())
    }

    type ConstructorPatRet = ();
    fn visit_constructor_pat(
        &self,
        _node: AstNodeRef<ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        Ok(())
    }
}
