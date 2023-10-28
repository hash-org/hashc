//! AST name checking.
//!
//! This module is responsible for performing lexical analysis on the Hash AST.
//! This includes:
//! - Resolving all names to their corresponding definitions.
//! - Gathering scopes of definitions and indexing them by AST node IDs.
//! - Checking for recursive definitions.
//! - Ensuring that there are no free variables in the AST.
use std::collections::{HashMap, HashSet};

use hash_ast::{
    ast::{
        self, AccessExpr, AccessPat, AccessTy, AstNode, AstNodeId, AstNodeRef, BindingPat,
        BodyBlock, CallExpr, ConstructorPat, Declaration, EnumDef, ExprArg, FnDef, FnTy,
        ImplicitFnCall, ImplicitFnDef, MatchCase, ModDef, Module, ModulePatEntry, NamedTy, Param,
        Params, StructDef, TuplePat, TupleTy, TyArg, TyParam, TyParams, VariableExpr,
    },
    ast_visitor_mut_self_default_impl,
    visitor::walk_mut_self,
};
use hash_source::identifier::Identifier;
use hash_utils::{fxhash::FxHashMap, scoping::ContextTypes};

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

/// A member of an AST scope.
#[derive(Debug, Clone)]
pub struct AstScopeMember {
    pub name: Identifier,
    pub defined_by: HashSet<AstNodeId>,
    pub referenced_by: HashSet<AstNodeId>,
}

/// An AST scope.
#[derive(Debug, Clone)]
pub struct AstScope {
    pub node: AstNodeId,
    pub members: HashMap<Identifier, AstScopeMember>,
}

impl AstScope {
    pub fn new(node: AstNodeId) -> Self {
        Self { node, members: HashMap::new() }
    }

    fn get_or_create_member(&mut self, ident: Identifier) -> &mut AstScopeMember {
        self.members.entry(ident).or_insert_with(|| AstScopeMember {
            name: ident,
            defined_by: HashSet::new(),
            referenced_by: HashSet::new(),
        })
    }

    pub fn register_reference(&mut self, node: &AstNode<ast::Name>) {
        let entry = self.get_or_create_member(node.ident);
        entry.referenced_by.insert(node.id());
    }

    pub fn register_definition(&mut self, node: &AstNode<ast::Name>) {
        let entry = self.get_or_create_member(node.ident);
        entry.defined_by.insert(node.id());
    }
}

/// The AST name data.
///
/// This is the result of the name checking pass on the AST.
///
/// It contains a record of all the scopes, definitions, and references
/// in the AST, indexed by the AST node ID of each relevant node.
#[derive(Debug, Clone, Default)]
pub struct AstNameData {
    scope_by_node: FxHashMap<AstNodeId, AstScope>,
    // Stores the declared members (as a `Scope`) of each scope-creating
    // AST node.
    //
    // Indexed by the following AST nodes:
    // `BodyBlock`, `Params`, `TyParams`, `Module`, `TupleLit`, `MatchCase`,
    // `FnDef`, `ImplicitFnDef`
    //scopes: FxHashMap<AstNodeId, Scope<AstContextTypes>>,
    // Stores the resolved name of each name-defining AST node.
    //
    // Indexed by the following AST nodes:
    // `Param`, `TyParam`, `TyArg`, `ExprArg`, `BindingPat` (optionally)
    //definitions: FxHashMap<AstNodeId, Name<AstContextTypes>>,
    // Stores the resolved name of each name-referencing AST node, including
    // the referencing mode for it.
    //
    // Indexed by the following AST nodes:
    // `VariableExpr`, `NamedTy`, `BindingPat` (optionally)
    // references: FxHashMap<AstNodeId, (Name<AstContextTypes>, ReferencingMode)>,
}

impl AstNameData {
    pub fn empty() -> Self {
        Self::default()
    }
}

pub(crate) struct AstNameDataVisitor<'n> {
    pub(crate) current_scopes: Vec<AstNodeId>,
    pub(crate) name_data: &'n mut AstNameData,
}

impl AstNameDataVisitor<'_> {
    fn current_scope_mut(&mut self) -> &mut AstScope {
        let id = *self.current_scopes.last().unwrap();
        self.name_data.scope_by_node.get_mut(&id).unwrap()
    }

    // fn discover_definition_from_name(
    //     &mut self,
    //     originating_node_id: AstNodeId,
    //     name: &AstNode<ast::Name>,
    // ) { let current_scope = self.context.get_current_scope_index().unwrap(); let
    //   member = self.context.search_member_in(current_scope, name.ident).unwrap();
    //   self.name_data.add_definition(originating_node_id, member);
    // }

    // fn discover_reference_from_name(
    //     &mut self,
    //     originating_node_id: AstNodeId,
    //     name: &AstNode<ast::Name>,
    // ) { let current_scope = self.context.get_current_scope_index().unwrap(); let
    //   member = self.context.search_member_in(current_scope, name.ident).unwrap();

    //     // @@Todo(mode): traverse delta-scopes and check if we are in a deferred
    // scope     // or not
    //     self.name_data.add_reference(originating_node_id, member,
    // ReferencingMode::Immediate); }
}

impl hash_ast::ast::AstVisitorMutSelf for AstNameDataVisitor<'_> {
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
        // match &node.name {
        //     Some(name) => self.discover_definition_from_name(node.id(), name),
        //     None => {}
        // }
        let _ = walk_mut_self::walk_param(self, node)?;
        Ok(())
    }

    type ExprArgRet = ();
    fn visit_expr_arg(
        &mut self,
        node: AstNodeRef<ExprArg>,
    ) -> Result<Self::ExprArgRet, Self::Error> {
        // match &node.name {
        //     Some(name) => self.discover_definition_from_name(node.id(), name),
        //     None => {}
        // }
        let _ = walk_mut_self::walk_expr_arg(self, node)?;
        Ok(())
    }

    type BindingPatRet = ();
    fn visit_binding_pat(
        &mut self,
        node: AstNodeRef<BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        // self.discover_definition_from_name(node.id(), &node.name);
        let _ = walk_mut_self::walk_binding_pat(self, node)?;
        Ok(())
    }

    // Scopes:

    type BodyBlockRet = ();
    fn visit_body_block(
        &mut self,
        node: AstNodeRef<BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        let _ = walk_mut_self::walk_body_block(self, node)?;
        Ok(())
    }

    // References:

    type VariableExprRet = ();
    fn visit_variable_expr(
        &mut self,
        node: AstNodeRef<VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        // self.discover_reference_from_name(node.id(), &node.name);
        let _ = walk_mut_self::walk_variable_expr(self, node)?;
        Ok(())
    }

    // @@Todo:

    type ImplicitFnDefRet = ();
    fn visit_implicit_fn_def(
        &mut self,
        node: AstNodeRef<ImplicitFnDef>,
    ) -> Result<Self::ImplicitFnDefRet, Self::Error> {
        let _ = walk_mut_self::walk_implicit_fn_def(self, node)?;
        Ok(())
    }

    type MatchCaseRet = ();
    fn visit_match_case(
        &mut self,
        node: AstNodeRef<MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let _ = walk_mut_self::walk_match_case(self, node)?;
        Ok(())
    }

    type FnDefRet = ();
    fn visit_fn_def(&mut self, node: AstNodeRef<FnDef>) -> Result<Self::FnDefRet, Self::Error> {
        let _ = walk_mut_self::walk_fn_def(self, node)?;
        Ok(())
    }

    type ModuleRet = ();
    fn visit_module(&mut self, node: AstNodeRef<Module>) -> Result<Self::ModuleRet, Self::Error> {
        let _ = walk_mut_self::walk_module(self, node)?;
        Ok(())
    }

    type TyArgRet = ();
    fn visit_ty_arg(&mut self, node: AstNodeRef<TyArg>) -> Result<Self::TyArgRet, Self::Error> {
        let _ = walk_mut_self::walk_ty_arg(self, node)?;
        Ok(())
    }

    type TyParamsRet = ();
    fn visit_ty_params(
        &mut self,
        node: AstNodeRef<TyParams>,
    ) -> Result<Self::TyParamsRet, Self::Error> {
        let _ = walk_mut_self::walk_ty_params(self, node)?;
        Ok(())
    }

    type ModDefRet = ();
    fn visit_mod_def(&mut self, node: AstNodeRef<ModDef>) -> Result<Self::ModDefRet, Self::Error> {
        let _ = walk_mut_self::walk_mod_def(self, node)?;
        Ok(())
    }

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

    type StructDefRet = ();
    fn visit_struct_def(
        &mut self,
        node: AstNodeRef<StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let _ = walk_mut_self::walk_struct_def(self, node)?;
        Ok(())
    }

    type FnTyRet = ();
    fn visit_fn_ty(&mut self, node: AstNodeRef<FnTy>) -> Result<Self::FnTyRet, Self::Error> {
        let _ = walk_mut_self::walk_fn_ty(self, node)?;
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

    type DeclarationRet = ();
    fn visit_declaration(
        &mut self,
        node: AstNodeRef<Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let _ = walk_mut_self::walk_declaration(self, node)?;
        Ok(())
    }

    type ParamsRet = ();
    fn visit_params(&mut self, node: AstNodeRef<Params>) -> Result<Self::ParamsRet, Self::Error> {
        let _ = walk_mut_self::walk_params(self, node)?;
        Ok(())
    }

    type EnumDefRet = ();
    fn visit_enum_def(
        &mut self,
        node: AstNodeRef<EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let _ = walk_mut_self::walk_enum_def(self, node)?;
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

    type NamedTyRet = ();
    fn visit_named_ty(
        &mut self,
        node: AstNodeRef<NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        let _ = walk_mut_self::walk_named_ty(self, node)?;
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

    type TyParamRet = ();
    fn visit_ty_param(
        &mut self,
        node: AstNodeRef<TyParam>,
    ) -> Result<Self::TyParamRet, Self::Error> {
        let _ = walk_mut_self::walk_ty_param(self, node)?;
        Ok(())
    }

    type TupleTyRet = ();
    fn visit_tuple_ty(
        &mut self,
        node: AstNodeRef<TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        let _ = walk_mut_self::walk_tuple_ty(self, node)?;
        Ok(())
    }
}
