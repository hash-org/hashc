//! AST name checking.
//!
//! This module is responsible for performing lexical analysis on the Hash AST.
//! This includes:
//! - Resolving all names to their corresponding definitions.
//! - Gathering scopes of definitions and indexing them by AST node IDs.
//! - Checking for recursive definitions.
//! - Ensuring that there are no free variables in the AST.
use std::convert::Infallible;

use hash_ast::{
    ast::{
        self, AccessExpr, AccessPat, AccessTy, AstNode, AstNodeId, AstNodeRef, BindingPat,
        BodyBlock, CallExpr, ConstructorPat, Declaration, EnumDef, ExprArg, FnDef, FnTy,
        ImplicitFnCall, ImplicitFnDef, MatchCase, ModDef, Module, ModulePatEntry, NamedTy, Param,
        Params, StructDef, TupleLit, TuplePat, TupleTy, TyArg, TyParam, TyParams, VariableExpr,
    },
    ast_visitor_mut_self_default_impl,
};
use hash_source::identifier::Identifier;
use hash_utils::{
    context::{Context, ContextTypes, Name, Scope},
    fxhash::FxHashMap,
};

/// The kind of scope that an AST node creates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AstScopeKind {
    /// A block `{}`.
    Block,
    /// A module.
    Mod,
    /// A match case.
    Match,
    /// Function parameters, tuple types, constructor types.
    Params,
    /// A tuple literal or constructor.
    Args,
    /// A deferred body, for functions.
    FnBody,
}

/// The referencing mode of a name in the AST.
/// @@Todo: possibly move this to `hash-utils`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReferencingMode {
    /// The name is referenced immediately.
    Immediate,
    /// The name is referenced in a deferred scope, so that recursive
    /// referencing is allowed.
    Deferred,
}

/// Container for the context types used for the AST.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AstContextTypes;
impl ContextTypes for AstContextTypes {
    type ScopeKind = AstScopeKind;
    type Value = ();
    type Symbol = Identifier;
}

/// The AST name data.
///
/// This is the result of the name checking pass on the AST.
///
/// It contains a record of all the scopes, definitions, and references
/// in the AST, indexed by the AST node ID of each relevant node.
#[derive(Debug, Clone, Default)]
pub struct AstNameData {
    /// Stores the declared members (as a `Scope`) of each scope-creating
    /// AST node.
    ///
    /// Indexed by the following AST nodes:
    /// `BodyBlock`, `Params`, `TyParams`, `Module`, `TupleLit`, `MatchCase`,
    /// `FnDef`, `ImplicitFnDef`
    scopes: FxHashMap<AstNodeId, Scope<AstContextTypes>>,
    /// Stores the resolved name of each name-defining AST node.
    ///
    /// Indexed by the following AST nodes:
    /// `Param`, `TyParam`, `TyArg`, `ExprArg`, `BindingPat` (optionally)
    definitions: FxHashMap<AstNodeId, Name<AstContextTypes>>,
    /// Stores the resolved name of each name-referencing AST node, including
    /// the referencing mode for it.
    ///
    /// Indexed by the following AST nodes:
    /// `VariableExpr`, `NamedTy`, `BindingPat` (optionally)
    references: FxHashMap<AstNodeId, (Name<AstContextTypes>, ReferencingMode)>,
}

impl AstNameData {
    /// Get the declared members (as a `Scope`) of the given scope-creating
    /// AST node.
    ///
    /// If the given AST node does not create a context, `None` is returned.
    pub fn get_scope(&self, node: AstNodeId) -> Option<&Scope<AstContextTypes>> {
        self.scopes.get(&node)
    }

    /// Get the resolved name of the given name-defining AST node.
    ///
    /// If the given AST node does not define a name, `None` is returned.
    pub fn get_definition(&self, node: AstNodeId) -> Option<&Name<AstContextTypes>> {
        self.definitions.get(&node)
    }

    /// Get the resolved name and referencing mode of the given name-referencing
    /// AST node.
    ///
    /// If the given AST node does not reference a name, `None` is returned.
    pub fn get_reference(
        &self,
        node: AstNodeId,
    ) -> Option<&(Name<AstContextTypes>, ReferencingMode)> {
        self.references.get(&node)
    }
}

impl AstNameData {
    fn new() -> Self {
        Self {
            scopes: FxHashMap::default(),
            definitions: FxHashMap::default(),
            references: FxHashMap::default(),
        }
    }

    fn add_scope(&mut self, node: AstNodeId, scope: Scope<AstContextTypes>) {
        self.scopes.insert(node, scope);
    }

    fn add_definition(&mut self, node: AstNodeId, name: Name<AstContextTypes>) {
        self.definitions.insert(node, name);
    }

    fn add_reference(
        &mut self,
        node: AstNodeId,
        name: Name<AstContextTypes>,
        mode: ReferencingMode,
    ) {
        self.references.insert(node, (name, mode));
    }
}

struct AstNameDataVisitor {
    context: Context<AstContextTypes>,
    name_data: AstNameData,
}

impl AstNameDataVisitor {
    fn discover_definition_from_name(
        &mut self,
        originating_node_id: AstNodeId,
        name: &AstNode<ast::Name>,
    ) {
        let current_scope = self.context.get_current_scope_index().unwrap();
        let member = self.context.search_member_in(current_scope, name.ident).unwrap();
        self.name_data.add_definition(originating_node_id, member);
    }

    fn discover_reference_from_name(
        &mut self,
        originating_node_id: AstNodeId,
        name: &AstNode<ast::Name>,
    ) {
        let current_scope = self.context.get_current_scope_index().unwrap();
        let member = self.context.search_member_in(current_scope, name.ident).unwrap();

        // @@Todo(mode): traverse delta-scopes and check if we are in a deferred scope
        // or not
        self.name_data.add_reference(originating_node_id, member, ReferencingMode::Immediate);
    }
}

impl hash_ast::ast::AstVisitorMutSelf for AstNameDataVisitor {
    type Error = Infallible;

    ast_visitor_mut_self_default_impl!(
      hiding: VariableExpr, BodyBlock, Params, TyParams, Param, TyParam, TyArg, ExprArg, StructDef,
      EnumDef, ImplicitFnDef, ModDef, FnDef, Module, TupleLit, TupleTy, FnTy, NamedTy, ImplicitFn,
      AccessTy, AccessExpr, Declaration, CallExpr, ImplicitFnCall, MatchCase, BindingPat,
      AccessPat, TuplePat, ConstructorPat, ModulePatEntry
    );

    type ParamRet = ();
    fn visit_param(&mut self, node: AstNodeRef<Param>) -> Result<Self::ParamRet, Self::Error> {
        match &node.name {
            Some(name) => self.discover_definition_from_name(node.id(), name),
            None => {}
        }
        Ok(())
    }

    type ExprArgRet = ();
    fn visit_expr_arg(
        &mut self,
        node: AstNodeRef<ExprArg>,
    ) -> Result<Self::ExprArgRet, Self::Error> {
        match &node.name {
            Some(name) => self.discover_definition_from_name(node.id(), name),
            None => {}
        }
        Ok(())
    }

    type VariableExprRet = ();
    fn visit_variable_expr(
        &mut self,
        node: AstNodeRef<VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        self.discover_reference_from_name(node.id(), &node.name);
        Ok(())
    }

    type ImplicitFnDefRet = ();
    fn visit_implicit_fn_def(
        &mut self,
        _node: AstNodeRef<ImplicitFnDef>,
    ) -> Result<Self::ImplicitFnDefRet, Self::Error> {
        todo!()
    }

    type MatchCaseRet = ();
    fn visit_match_case(
        &mut self,
        _node: AstNodeRef<MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        todo!()
    }

    type FnDefRet = ();

    fn visit_fn_def(&mut self, _node: AstNodeRef<FnDef>) -> Result<Self::FnDefRet, Self::Error> {
        todo!()
    }

    type ModuleRet = ();

    fn visit_module(&mut self, _node: AstNodeRef<Module>) -> Result<Self::ModuleRet, Self::Error> {
        todo!()
    }

    type TyArgRet = ();

    fn visit_ty_arg(&mut self, _node: AstNodeRef<TyArg>) -> Result<Self::TyArgRet, Self::Error> {
        todo!()
    }

    type TyParamsRet = ();

    fn visit_ty_params(
        &mut self,
        _node: AstNodeRef<TyParams>,
    ) -> Result<Self::TyParamsRet, Self::Error> {
        todo!()
    }

    type ModDefRet = ();

    fn visit_mod_def(&mut self, _node: AstNodeRef<ModDef>) -> Result<Self::ModDefRet, Self::Error> {
        todo!()
    }

    type AccessPatRet = ();

    fn visit_access_pat(
        &mut self,
        _node: AstNodeRef<AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        todo!()
    }

    type TupleLitRet = ();

    fn visit_tuple_lit(
        &mut self,
        _node: AstNodeRef<TupleLit>,
    ) -> Result<Self::TupleLitRet, Self::Error> {
        todo!()
    }

    type AccessExprRet = ();

    fn visit_access_expr(
        &mut self,
        _node: AstNodeRef<AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        todo!()
    }

    type TuplePatRet = ();

    fn visit_tuple_pat(
        &mut self,
        _node: AstNodeRef<TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        todo!()
    }

    type StructDefRet = ();

    fn visit_struct_def(
        &mut self,
        _node: AstNodeRef<StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        todo!()
    }

    type FnTyRet = ();

    fn visit_fn_ty(&mut self, _node: AstNodeRef<FnTy>) -> Result<Self::FnTyRet, Self::Error> {
        todo!()
    }

    type AccessTyRet = ();

    fn visit_access_ty(
        &mut self,
        _node: AstNodeRef<AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        todo!()
    }

    type ConstructorPatRet = ();

    fn visit_constructor_pat(
        &mut self,
        _node: AstNodeRef<ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        todo!()
    }

    type DeclarationRet = ();

    fn visit_declaration(
        &mut self,
        _node: AstNodeRef<Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        todo!()
    }

    type ParamsRet = ();

    fn visit_params(&mut self, _node: AstNodeRef<Params>) -> Result<Self::ParamsRet, Self::Error> {
        todo!()
    }

    type EnumDefRet = ();

    fn visit_enum_def(
        &mut self,
        _node: AstNodeRef<EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        todo!()
    }

    type ModulePatEntryRet = ();

    fn visit_module_pat_entry(
        &mut self,
        _node: AstNodeRef<ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error> {
        todo!()
    }

    type BindingPatRet = ();

    fn visit_binding_pat(
        &mut self,
        _node: AstNodeRef<BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        todo!()
    }

    type NamedTyRet = ();

    fn visit_named_ty(
        &mut self,
        _node: AstNodeRef<NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        todo!()
    }

    type ImplicitFnCallRet = ();

    fn visit_implicit_fn_call(
        &mut self,
        _node: AstNodeRef<ImplicitFnCall>,
    ) -> Result<Self::ImplicitFnCallRet, Self::Error> {
        todo!()
    }

    type CallExprRet = ();

    fn visit_call_expr(
        &mut self,
        _node: AstNodeRef<CallExpr>,
    ) -> Result<Self::CallExprRet, Self::Error> {
        todo!()
    }

    type TyParamRet = ();

    fn visit_ty_param(
        &mut self,
        _node: AstNodeRef<TyParam>,
    ) -> Result<Self::TyParamRet, Self::Error> {
        todo!()
    }

    type TupleTyRet = ();

    fn visit_tuple_ty(
        &mut self,
        _node: AstNodeRef<TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        todo!()
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &mut self,
        _node: AstNodeRef<BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        todo!()
    }
}
