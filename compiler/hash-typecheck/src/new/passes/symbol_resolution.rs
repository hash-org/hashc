use std::collections::HashMap;

/// The second pass of the typechecker, which resolves all symbols to their
/// referenced bindings.
///
/// Any scoping errors are reported here.
use hash_ast::{
    ast, ast_visitor_default_impl,
    visitor::{walk, AstVisitor},
};
use hash_source::identifier::Identifier;
use hash_types::new::{
    environment::{
        context::{BindingKind, ScopeKind},
        env::AccessToEnv,
    },
    mods::ModMemberValue,
    scopes::{BoundVar, StackMemberId},
    symbols::Symbol,
    terms::Term,
};
use hash_utils::store::{CloneStore, SequenceStore, Store};

use super::{
    ast_pass::AstPass,
    state::{HeavyState, LightState},
};
use crate::{
    impl_access_to_tc_env,
    new::{
        diagnostics::error::TcError,
        environment::tc_env::{AccessToTcEnv, TcEnv},
        ops::{ast::AstOps, common::CommonOps, AccessToOps},
    },
};

/// The current expression kind we are in.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InExpr {
    /// We are in a type expression.
    Type,
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
enum AstArgGroup<'a> {
    /// A group of explicit `(a, b, c)` arguments.
    ExplicitArgs(&'a ast::AstNodes<ast::ConstructorCallArg>),
    /// A group of implicit `<a, b, c>` arguments.
    ImplicitArgs(&'a ast::AstNodes<ast::TyArg>),
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
    pub(self) name: Symbol,
    pub(self) args: Vec<AstArgGroup<'a>>,
}

impl<'tc> SymbolResolutionPass<'tc> {
    fn resolve_ast_path_component(
        &self,
        _component: AstPathComponent<'_>,
        starting_from: Option<ModMemberValue>,
        _in_expr: InExpr,
    ) {
        match starting_from {
            Some(_) => todo!(),
            None => todo!(),
        }
    }

    fn resolve_ast_path(&self, path: Vec<AstPathComponent<'_>>, _in_expr: InExpr) {
        for _component in &path {}
    }
}

/// @@Temporary: for now this visitor just walks the AST and enters scopes. The
/// next step is to resolve symbols in these scopes!.
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
        COnstructorPat,
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
        self.in_expr.enter(InExpr::Type, || walk::walk_ty(self, node))?;
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
        let var_name = node.name.ident;

        // Try to lookup the variable in the current scope.
        match self.lookup_binding_by_name(var_name) {
            Some(binding_symbol) => {
                let member = self.context().get_binding(binding_symbol).unwrap();
                match member.kind {
                    BindingKind::ModMember(_, mod_member) => {
                        // This is a module member, so we need to check that it is
                        // valid in expression position.
                        let member_term = self.stores().mod_members().get_element(mod_member);
                        match member_term.value {
                            ModMemberValue::Data(_) => {
                                // Cannot use a data type in a value position.
                                // Constructor calls are handled by `TyFnCall`
                                // and
                                // `ConstructorCall` visits.
                                //
                                // To reference the type, we should be in a
                                // type context instead.
                                self.diagnostics().add_error(
                                    TcError::CannotUseDataTypeInValuePosition {
                                        location: self.node_location(node),
                                    },
                                );
                            }
                            ModMemberValue::Mod(_) => {
                                // Cannot use a module in a value position.
                                self.diagnostics().add_error(
                                    TcError::CannotUseModuleInValuePosition {
                                        location: self.node_location(node),
                                    },
                                );
                            }
                            ModMemberValue::Fn(fn_def_id) => {
                                // If a function is used in a value position, then it is
                                // the function's address that is used.
                                self.ast_info()
                                    .terms()
                                    .insert(node.id(), self.new_term(Term::FnRef(fn_def_id)));
                            }
                        }
                    }
                    BindingKind::Ctor(_, _) => {
                        // This is a constructor, so we need to check that it is
                        // a unit constructor.
                        todo!()
                    }
                    BindingKind::BoundVar(bound_var_origin) => {
                        // A bound variable can be used in expression position.
                        // Further typechecking will ensure this is valid.
                        self.ast_info().terms().insert(
                            node.id(),
                            self.new_term(Term::Var(BoundVar {
                                name: binding_symbol,
                                origin: bound_var_origin,
                            })),
                        );
                    }
                }
            }
            None => {
                // Symbol not found.
                self.diagnostics().add_error(TcError::SymbolNotFound {
                    symbol: self.new_symbol(var_name),
                    location: self.node_location(node),
                });
            }
        }

        Ok(())
    }

    type NamedTyRet = ();
    fn visit_named_ty(
        &self,
        node: ast::AstNodeRef<ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        let var_name = node.name.ident;
        match self.lookup_binding_by_name(var_name) {
            Some(binding_symbol) => {
                println!("binding: {binding_symbol:?}");
                Ok(())
            }
            None => {
                // @@Todo: diagnostics
                println!("unbound variable: {var_name}");
                Ok(())
            }
        }
    }

    type AccessTyRet = ();
    fn visit_access_ty(
        &self,
        _node: ast::AstNodeRef<ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
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
        _node: ast::AstNodeRef<ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        Ok(())
    }
}
