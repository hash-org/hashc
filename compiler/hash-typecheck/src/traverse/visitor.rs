//! Contains functions to traverse the AST and add types to it, while checking
//! it for correctness.

use std::{iter, mem};

use hash_ast::{
    ast::{
        self, AccessKind, AstNodeRef, BinOp, Lit, MatchOrigin, OwnsAstNode, ParamOrigin, RefKind,
        UnOp,
    },
    visitor::{self, walk, AstVisitor},
};
use hash_pipeline::sources::{NodeMap, SourceRef};
use hash_reporting::{diagnostic::Diagnostics, macros::panic_on_span};
use hash_source::{
    identifier::{Identifier, CORE_IDENTIFIERS},
    location::{SourceLocation, Span},
    ModuleKind, SourceId,
};
use hash_utils::store::{PartialStore, Store};
use itertools::Itertools;

use super::{scopes::VisitConstantScope, AccessToTraverseOps};
use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::tc_panic,
        warning::TcWarning,
    },
    ops::{scope::ScopeManager, AccessToOps},
    storage::{
        location::{IndexedLocationTarget, LocationTarget},
        nodes::NodeInfoTarget,
        nominals::NominalDefId,
        pats::PatId,
        primitives::{
            AccessOp, Arg, BindingPat, ConstPat, Field, Member, ModDefOrigin, Mutability, Param,
            Pat, PatArg, RangePat, ScopeKind, SpreadPat, Sub, Visibility,
        },
        terms::TermId,
        AccessToStorage, LocalStorage, StorageRef,
    },
};

/// Internal state that the [TcVisitor] uses when traversing the
/// given sources.
#[derive(Default)]
pub struct TcVisitorState {
    /// Pattern hint from declaration
    pub declaration_name_hint: Option<Identifier>,
    /// Return type for functions with return statements
    pub fn_def_return_ty: Option<TermId>,
    /// If the current traversal is within the intrinsic directive scope.
    pub within_intrinsics_directive: bool,
    /// If traversing a declaration, what to set for the
    /// `assignments_until_closed` field.
    pub declaration_assignments_until_closed: usize,
}

impl TcVisitorState {
    /// Create a new [TcVisitorState]
    pub fn new() -> Self {
        Self::default()
    }
}

/// Traverses the AST and adds types to it, while checking it for correctness.
///
/// Contains typechecker state that is accessed while traversing.
pub struct TcVisitor<'tc> {
    pub storage: StorageRef<'tc>,
    pub node_map: &'tc NodeMap,
    pub state: TcVisitorState,
}

impl<'tc> AccessToStorage for TcVisitor<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> TcVisitor<'tc> {
    /// Create a new [TcVisitor] with the given state, traversing the given
    /// source from [SourceId].
    pub fn new_in_source(storage: StorageRef<'tc>, node_map: &'tc NodeMap) -> Self {
        TcVisitor { storage, node_map, state: TcVisitorState::new() }
    }

    /// Visits the source passed in as an argument to [Self::new_in_source], and
    /// returns the term of the module that corresponds to the source.
    pub fn visit_source(&mut self) -> TcResult<TermId> {
        let source_id = self.local_storage().current_source();
        let source = self.node_map.get_source(source_id);

        let result = match source {
            SourceRef::Interactive(interactive_source) => {
                self.visit_body_block(&(), interactive_source.node_ref())
            }
            SourceRef::Module(module_source) => self.visit_module(&(), module_source.node_ref()),
        }?;

        // Add the result to the checked sources.
        // @@Correctness: the visitor will loop infinitely if there are circular module
        // dependencies. Need to find a way to prevent this.
        self.checked_sources().mark_checked(source_id, result);

        log::debug!(
            "tc cache metrics:\n{: <8}: {}\n{: <8}: {}\n{: <8}: {}\n{: <8}: {}\n",
            "simplify",
            self.cache().simplification_store.metrics(),
            "validate",
            self.cache().validation_store.metrics(),
            "unify",
            self.cache().unification_store.metrics(),
            "infer",
            self.cache().inference_store.metrics()
        );

        Ok(result)
    }

    /// Create a [SourceLocation] from a [Span].
    pub(crate) fn source_location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, id: self.local_storage().current_source() }
    }

    /// Create a [SourceLocation] at the given [hash_ast::ast::AstNode].
    pub(crate) fn source_location_at_node<N>(&self, node: AstNodeRef<N>) -> SourceLocation {
        let node_span = node.span();
        self.source_location(node_span)
    }

    /// Copy the [SourceLocation] of the given [hash_ast::ast::AstNode] to the
    /// given [LocationTarget].
    pub(crate) fn copy_location_from_node_to_target<N>(
        &self,
        node: AstNodeRef<N>,
        target: impl Into<LocationTarget>,
    ) {
        let location = self.source_location_at_node(node);
        self.location_store().add_location_to_target(target, location);
    }

    /// Copy the [SourceLocation] of the given [hash_ast::ast::AstNode] list to
    /// the given [LocationTarget] list represented by a type `Target` where
    /// `(Target, usize)` implements [Into<LocationTarget>].
    pub(crate) fn copy_location_from_nodes_to_targets<'n, N: 'n>(
        &self,
        nodes: impl IntoIterator<Item = AstNodeRef<'n, N>>,
        targets: impl Into<IndexedLocationTarget> + Clone,
    ) {
        let targets = targets.into();
        for (index, param) in nodes.into_iter().enumerate() {
            self.copy_location_from_node_to_target(param, LocationTarget::from((targets, index)));
        }
    }

    /// Register the given [`TermId`] or [`PatId`] as describing the given
    /// [AstNodeRef].
    ///
    /// This copies the node's location to the term, and adds the node-term pair
    /// to [crate::storage::NodeInfoStore].
    fn register_node_info<T>(
        &self,
        node: AstNodeRef<T>,
        data: impl Into<NodeInfoTarget> + Into<LocationTarget> + Clone,
    ) {
        self.copy_location_from_node_to_target(node, data.clone());
        self.node_info_store().insert(node.id(), data.into());
    }

    /// Validate and register node info for the given term.
    fn validate_and_register_simplified_term<T>(
        &self,
        node: AstNodeRef<T>,
        term: TermId,
    ) -> TcResult<TermId> {
        // Copy location before so that validation errors point to the right location:
        self.copy_location_from_node_to_target(node, term);

        let simplified_term_id = self.validator().validate_term(term)?.simplified_term_id;
        self.node_info_store().insert(node.id(), NodeInfoTarget::Term(simplified_term_id));
        Ok(simplified_term_id)
    }
}

/// Implementation of [visitor::AstVisitor] for [TcVisitor], to traverse the AST
/// and type it.
///
/// Notes:
/// - Terms derived from expressions are always validated, in order to ensure
///   they are correct. The same goes for types.
impl<'tc> visitor::AstVisitor for TcVisitor<'tc> {
    type Ctx = ();
    type CollectionContainer<T> = Vec<T>;

    fn try_collect_items<T, E, I: Iterator<Item = Result<T, E>>>(
        _: &Self::Ctx,
        items: I,
    ) -> Result<Self::CollectionContainer<T>, E> {
        items.collect()
    }

    type Error = TcError;

    type NameRet = Identifier;

    fn visit_name(
        &mut self,
        _: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        Ok(node.ident)
    }

    type LitRet = TermId;

    fn visit_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Lit>,
    ) -> Result<Self::LitRet, Self::Error> {
        walk::walk_lit_same_children(self, ctx, node)
    }

    type MapLitRet = TermId;

    fn visit_map_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLit>,
    ) -> Result<Self::MapLitRet, Self::Error> {
        let walk::MapLit { entries } = walk::walk_map_lit(self, ctx, node)?;
        let map_inner_ty = self.core_defs().map_ty_fn();

        // Unify the key and value types...
        let key_ty = self.unifier().unify_rt_term_sequence(entries.iter().map(|(k, _)| *k))?;
        let val_ty = self.unifier().unify_rt_term_sequence(entries.iter().map(|(v, _)| *v))?;

        let builder = self.builder();
        let map_ty = builder.create_app_ty_fn_term(
            map_inner_ty,
            builder.create_args(
                [builder.create_arg("K", key_ty), builder.create_arg("V", val_ty)],
                ParamOrigin::TyFn,
            ),
        );

        let term = builder.create_rt_term(map_ty);
        self.register_node_info(node, term);
        Ok(term)
    }

    type MapLitEntryRet = (TermId, TermId);

    fn visit_map_lit_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLitEntry>,
    ) -> Result<Self::MapLitEntryRet, Self::Error> {
        let walk::MapLitEntry { key, value } = walk::walk_map_lit_entry(self, ctx, node)?;

        Ok((key, value))
    }

    type ListLitRet = TermId;

    fn visit_list_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListLit>,
    ) -> Result<Self::ListLitRet, Self::Error> {
        let walk::ListLit { elements } = walk::walk_list_lit(self, ctx, node)?;

        let list_inner_ty = self.core_defs().list_ty_fn();
        let element_ty = self.unifier().unify_rt_term_sequence(elements)?;

        let builder = self.builder();
        let list_ty = builder.create_app_ty_fn_term(
            list_inner_ty,
            builder.create_args([builder.create_arg("T", element_ty)], ParamOrigin::TyFn),
        );

        let term = builder.create_rt_term(list_ty);
        self.register_node_info(node, term);
        Ok(term)
    }

    type SetLitRet = TermId;

    fn visit_set_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::SetLit>,
    ) -> Result<Self::SetLitRet, Self::Error> {
        let walk::SetLit { elements } = walk::walk_set_lit(self, ctx, node)?;

        let set_inner_ty = self.core_defs().set_ty_fn();
        let element_ty = self.unifier().unify_rt_term_sequence(elements)?;

        let builder = self.builder();
        let set_ty = builder.create_app_ty_fn_term(
            set_inner_ty,
            builder.create_args([builder.create_arg("T", element_ty)], ParamOrigin::TyFn),
        );

        let term = builder.create_rt_term(set_ty);
        self.register_node_info(node, term);
        Ok(term)
    }

    type TupleLitEntryRet = Arg;

    fn visit_tuple_lit_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLitEntry>,
    ) -> Result<Self::TupleLitEntryRet, Self::Error> {
        let walk::TupleLitEntry { name, value, ty } = walk::walk_tuple_lit_entry(self, ctx, node)?;

        let ty_or_unresolved = ty.unwrap_or_else(|| self.builder().create_unresolved_term());
        let value_ty = self.typer().infer_ty_of_term(value)?;
        self.register_node_info(node.value.ast_ref(), value_ty);

        // Check that the type of the value and the type annotation match and then apply
        // the substitution onto ty
        let ty_sub = self.unifier().unify_terms(value_ty, ty_or_unresolved)?;
        let value = self.substituter().apply_sub_to_term(&ty_sub, value);

        Ok(Arg { name, value })
    }

    type TupleLitRet = TermId;

    fn visit_tuple_lit(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLit>,
    ) -> Result<Self::TupleLitRet, Self::Error> {
        let walk::TupleLit { elements } = walk::walk_tuple_lit(self, ctx, node)?;
        let builder = self.builder();

        let params = builder.create_args(elements, ParamOrigin::Tuple);
        let term = builder.create_tuple_lit_term(params);

        // add the location of each parameter, and the term, to the location storage
        self.copy_location_from_nodes_to_targets(node.elements.ast_ref_iter(), params);
        self.register_node_info(node, term);

        Ok(term)
    }

    type StrLitRet = TermId;

    fn visit_str_lit(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::StrLit>,
    ) -> Result<Self::StrLitRet, Self::Error> {
        let term = self.builder().create_lit_term(node.0.to_string());
        self.register_node_info(node, term);
        Ok(term)
    }

    type CharLitRet = TermId;

    fn visit_char_lit(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::CharLit>,
    ) -> Result<Self::CharLitRet, Self::Error> {
        let term = self.builder().create_lit_term(node.0);
        self.register_node_info(node, term);
        Ok(term)
    }

    type FloatLitRet = TermId;

    fn visit_float_lit(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error> {
        let f32_def = self.core_defs().f32_ty();
        let term = self.builder().create_rt_term(f32_def);
        self.register_node_info(node, term);
        Ok(term)
    }

    type BoolLitRet = TermId;

    fn visit_bool_lit(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BoolLit>,
    ) -> Result<Self::BoolLitRet, Self::Error> {
        let term = self.builder().create_var_term(if node.0 {
            CORE_IDENTIFIERS.r#true
        } else {
            CORE_IDENTIFIERS.r#false
        });
        self.validate_and_register_simplified_term(node, term)
    }

    type IntLitRet = TermId;

    fn visit_int_lit(
        &mut self,
        _: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IntLit>,
    ) -> Result<Self::IntLitRet, Self::Error> {
        let term = self.builder().create_lit_term(node.body().clone());
        self.register_node_info(node, term);
        Ok(term)
    }

    type BinOpRet = ();

    fn visit_bin_op(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BinOp>,
    ) -> Result<Self::BinOpRet, Self::Error> {
        Ok(())
    }

    type UnOpRet = ();

    fn visit_un_op(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnOp>,
    ) -> Result<Self::UnOpRet, Self::Error> {
        Ok(())
    }

    type ExprRet = TermId;

    fn visit_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Expr>,
    ) -> Result<Self::ExprRet, Self::Error> {
        let term_id = walk::walk_expr_same_children(self, ctx, node)?;
        // Since this is an expression, we want to coerce the term to a value if
        // applicable:
        Ok(self.coercing().potentially_coerce_as_value(term_id, node))
    }

    type VariableExprRet = TermId;

    fn visit_variable_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        let walk::VariableExpr { name } = walk::walk_variable_expr(self, ctx, node)?;
        let term = self.builder().create_var_term(name);
        self.validate_and_register_simplified_term(node, term)
    }

    type DirectiveExprRet = TermId;

    fn visit_directive_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let old_intrinsics_state = self.state.within_intrinsics_directive;

        // If the current specified directive is `intrinsics`, then we have to enable
        // the flag `within_intrinsics_directive` which changes the way that `mod`
        // blocks are validated and changes the parsing of the declarations inside the
        // mod block.
        if node.name.is(CORE_IDENTIFIERS.intrinsics) {
            self.state.within_intrinsics_directive = true;
        }

        // @@Directives: Decide on what to do with directives, but for now walk the
        // inner types...
        let walk::DirectiveExpr { subject, .. } = walk::walk_directive_expr(self, ctx, node)?;

        self.state.within_intrinsics_directive = old_intrinsics_state;

        self.register_node_info(node, subject);
        Ok(subject)
    }

    type ConstructorCallArgRet = Arg;

    fn visit_constructor_call_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error> {
        let walk::ConstructorCallArg { name, value } =
            walk::walk_constructor_call_arg(self, ctx, node)?;
        Ok(Arg { name, value })
    }

    type ConstructorCallExprRet = TermId;

    fn visit_constructor_call_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        let walk::ConstructorCallExpr { args, subject } =
            walk::walk_constructor_call_expr(self, ctx, node)?;

        // Create the args with origin as `FnCall`, although it might be altered
        // when the term is simplified into `Struct` or `Enum` variant.
        let args = self.builder().create_args(args, ParamOrigin::FnCall);
        self.copy_location_from_nodes_to_targets(node.args.ast_ref_iter(), args);

        // Create the function call term:
        let return_term = self.builder().create_fn_call_term(subject, args);

        self.validate_and_register_simplified_term(node, return_term)
    }

    type PropertyKindRet = Field;

    fn visit_property_kind(
        &mut self,
        _: &Self::Ctx,
        node: ast::AstNodeRef<ast::PropertyKind>,
    ) -> Result<Self::PropertyKindRet, Self::Error> {
        Ok(match node.body() {
            ast::PropertyKind::NamedField(name) => Field::Named(*name),
            ast::PropertyKind::NumericField(index) => Field::Numeric(*index),
        })
    }

    type AccessExprRet = TermId;

    fn visit_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        let walk::AccessExpr { subject, property, kind } = walk::walk_access_expr(self, ctx, node)?;
        let term = self.builder().create_access(subject, property, kind);
        self.validate_and_register_simplified_term(node, term)
    }

    type AccessKindRet = AccessOp;

    fn visit_access_kind(
        &mut self,
        _: &Self::Ctx,
        node: hash_ast::ast::AccessKind,
    ) -> Result<Self::AccessKindRet, Self::Error> {
        match node {
            AccessKind::Namespace => Ok(AccessOp::Namespace),
            AccessKind::Property => Ok(AccessOp::Property),
        }
    }

    type RefExprRet = TermId;

    fn visit_ref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let walk::RefExpr { inner_expr, mutability } = walk::walk_ref_expr(self, ctx, node)?;

        // Depending on the `mutability` of the reference, create the relevant type
        // function application
        let ref_def = if mutability.is_some() {
            self.core_defs().reference_mut_ty_fn()
        } else {
            self.core_defs().reference_ty_fn()
        };

        let builder = self.builder();

        // Create either `RefMut<T>` or `Ref<T>`
        let ref_args =
            builder.create_args([builder.create_arg("T", inner_expr)], ParamOrigin::TyFn);
        let ref_ty = builder.create_app_ty_fn_term(ref_def, ref_args);

        let term = builder.create_rt_term(ref_ty);

        self.validate_and_register_simplified_term(node, term)
    }

    type DerefExprRet = TermId;

    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let walk::DerefExpr(inner) = walk::walk_deref_expr(self, ctx, node)?;
        let inner_ty = self.typer().infer_ty_of_term(inner)?;

        // Create a `Ref<T>` dummy type for unification...
        let ap_ref_ty = {
            let ref_ty = self.core_defs().reference_ty_fn();
            let builder = self.builder();

            builder.create_app_ty_fn_term(
                ref_ty,
                builder.create_args(
                    [builder.create_arg("T", builder.create_unresolved_term())],
                    ParamOrigin::TyFn,
                ),
            )
        };

        // Create a `RefMut<T>` dummy type for unification...
        let ap_ref_mut_ty = {
            let ref_mut_ty = self.core_defs().reference_mut_ty_fn();
            let builder = self.builder();

            builder.create_app_ty_fn_term(
                ref_mut_ty,
                builder.create_args(
                    [builder.create_arg("T", builder.create_unresolved_term())],
                    ParamOrigin::TyFn,
                ),
            )
        };

        // Attempt to unify this with a `Ref<T>` to see if the `inner_ty` can
        // be dereferenced. If that fails, then try to unify with `RefMut<T>`
        //
        // @@Todo(feds01): Add a custom error type that says the desired type cannot be
        // dereferenced
        let result = self
            .unifier()
            .unify_terms(inner_ty, ap_ref_ty)
            .or_else(|_| self.unifier().unify_terms(inner_ty, ap_ref_mut_ty))?;

        // get the substitution result and use that as the return from the `inner_ty`
        let inner_ty = result.pairs().next().unwrap().1;

        let term = self.builder().create_rt_term(inner_ty);

        self.validate_and_register_simplified_term(node, term)
    }

    type UnsafeExprRet = TermId;

    fn visit_unsafe_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error> {
        // @@UnsafeExprs: Decide on what to do with unsafe expressions, but for now walk
        // the inner types...
        let walk::UnsafeExpr(subject) = walk::walk_unsafe_expr(self, ctx, node)?;
        Ok(subject)
    }

    type LitExprRet = TermId;

    fn visit_lit_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::LitExpr>,
    ) -> Result<Self::LitExprRet, Self::Error> {
        Ok(walk::walk_lit_expr(self, ctx, node)?.0)
    }

    type CastExprRet = TermId;

    fn visit_cast_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        let walk::CastExpr { expr, ty } = walk::walk_cast_expr(self, ctx, node)?;
        let expr_ty = self.typer().infer_ty_of_term(expr)?;

        // Ensure that the `expr` can be unified with the provided `ty`...
        let sub = self.unifier().unify_terms(expr_ty, ty)?;

        // Return Rt(..) of the ty:
        let term = self.substituter().apply_sub_to_term(&sub, self.builder().create_rt_term(ty));
        self.validate_and_register_simplified_term(node, term)
    }

    type TyExprRet = TermId;

    fn visit_ty_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TyExpr>,
    ) -> Result<Self::TyExprRet, Self::Error> {
        Ok(walk::walk_ty_expr(self, ctx, node)?.0)
    }

    type BlockExprRet = TermId;

    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        Ok(walk::walk_block_expr(self, ctx, node)?.0)
    }

    type ImportRet = TermId;

    fn visit_import(
        &mut self,
        _: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        // Try resolve the path of the import to a SourceId:
        let import_module_id = self.source_map().get_module_id_by_path(&node.resolved_path);
        match import_module_id {
            Some(import_module_id) => {
                let id = SourceId::Module(import_module_id);

                // Resolve the ModDef corresponding to the SourceId if it exists:
                match self.checked_sources().source_mod_def(id) {
                    Some(already_checked_mod_term) => {
                        // Already exists, meaning this module has been checked before:
                        Ok(already_checked_mod_term)
                    }
                    None => {
                        // Module has not been checked before, time to check it:

                        // First, create a new storage reference for the child module:
                        let node_map = self.node_map;
                        let storage_ref = self.storages();
                        let child_local_storage = LocalStorage::new(storage_ref.global_storage, id);
                        let child_storage_ref =
                            StorageRef { local_storage: &child_local_storage, ..storage_ref };

                        // Visit the child module
                        let mut child_visitor =
                            TcVisitor::new_in_source(child_storage_ref, node_map);
                        let module_term = child_visitor.visit_source()?;
                        Ok(module_term)
                    }
                }
            }
            None => {
                // This should never happen because all modules should have been parsed by now.
                let unresolved_import_term = self.builder().create_unresolved_term();
                self.register_node_info(node, unresolved_import_term);
                tc_panic!(
                    unresolved_import_term,
                    self,
                    "Found import path that hasn't been resolved to a module!"
                )
            }
        }
    }

    type ImportExprRet = TermId;

    fn visit_import_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        Ok(walk::walk_import_expr(self, ctx, node)?.0)
    }

    type TyRet = TermId;

    fn visit_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Ty>,
    ) -> Result<Self::TyRet, Self::Error> {
        walk::walk_ty_same_children(self, ctx, node)
    }

    type TupleTyRet = TermId;

    fn visit_tuple_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        let walk::TupleTy { entries } = walk::walk_tuple_ty(self, ctx, node)?;

        let members = self.builder().create_params(entries, ParamOrigin::Tuple);
        self.copy_location_from_nodes_to_targets(node.entries.ast_ref_iter(), members);
        let term = self.builder().create_tuple_ty_term(members);

        self.validate_and_register_simplified_term(node, term)
    }

    type ListTyRet = TermId;

    fn visit_list_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListTy>,
    ) -> Result<Self::ListTyRet, Self::Error> {
        let walk::ListTy { inner } = walk::walk_list_ty(self, ctx, node)?;

        let inner_ty = self.core_defs().list_ty_fn();
        let builder = self.builder();

        let term = builder.create_app_ty_fn_term(
            inner_ty,
            builder.create_args([builder.create_arg("T", inner)], ParamOrigin::TyFn),
        );

        self.validate_and_register_simplified_term(node, term)
    }

    type SetTyRet = TermId;

    fn visit_set_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::SetTy>,
    ) -> Result<Self::SetTyRet, Self::Error> {
        let walk::SetTy { inner } = walk::walk_set_ty(self, ctx, node)?;

        let inner_ty = self.core_defs().set_ty_fn();
        let builder = self.builder();

        let term = builder.create_app_ty_fn_term(
            inner_ty,
            builder.create_args([builder.create_arg("T", inner)], ParamOrigin::TyFn),
        );

        self.validate_and_register_simplified_term(node, term)
    }

    type MapTyRet = TermId;

    fn visit_map_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapTy>,
    ) -> Result<Self::MapTyRet, Self::Error> {
        let walk::MapTy { key, value } = walk::walk_map_ty(self, ctx, node)?;

        let inner_ty = self.core_defs().map_ty_fn();
        let builder = self.builder();

        let term = builder.create_app_ty_fn_term(
            inner_ty,
            builder.create_args(
                [builder.create_arg("K", key), builder.create_arg("V", value)],
                ParamOrigin::TyFn,
            ),
        );

        self.validate_and_register_simplified_term(node, term)
    }

    type TyArgRet = Param;

    fn visit_ty_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error> {
        let walk::TyArg { ty, name } = walk::walk_ty_arg(self, ctx, node)?;
        self.register_node_info(node, ty);
        Ok(Param { ty, name, default_value: None })
    }

    type FnTyRet = TermId;

    fn visit_fn_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FnTy>,
    ) -> Result<Self::FnTyRet, Self::Error> {
        let walk::FnTy { params, return_ty } = walk::walk_fn_ty(self, ctx, node)?;
        let params = self.builder().create_params(params, ParamOrigin::Fn);

        // Add all the locations to the parameters:
        self.copy_location_from_nodes_to_targets(node.params.ast_ref_iter(), params);

        // Create the function type term:
        let fn_ty_term = self.builder().create_fn_ty_term(params, return_ty);

        self.validate_and_register_simplified_term(node, fn_ty_term)
    }

    type TyFnRet = TermId;

    fn visit_ty_fn_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TyFn>,
    ) -> Result<Self::TyFnRet, Self::Error> {
        let params = Self::try_collect_items(
            ctx,
            node.params.iter().map(|a| self.visit_param(ctx, a.ast_ref())),
        )?;
        let params = self.builder().create_params(params, ParamOrigin::TyFn);

        let param_scope = self.scope_manager().make_bound_scope(params);
        let return_value = ScopeManager::enter_scope_with(self, param_scope, |this| {
            this.visit_ty(ctx, node.return_ty.ast_ref())
        })?;

        // Add all the locations to the parameters:
        self.copy_location_from_nodes_to_targets(node.params.ast_ref_iter(), params);

        // Create the type function type term:
        let ty_fn_ty_term = self.builder().create_ty_fn_ty_term(params, return_value);

        self.validate_and_register_simplified_term(node, ty_fn_ty_term)
    }

    type TyFnCallRet = TermId;

    fn visit_ty_fn_call(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TyFnCall>,
    ) -> Result<Self::TyFnCallRet, Self::Error> {
        let walk::TyFnCall { args, subject } = walk::walk_ty_fn_call(self, ctx, node)?;

        // These should be converted to args
        let args = self.builder().create_args(
            args.iter().map(|param_arg| Arg { name: param_arg.name, value: param_arg.ty }),
            ParamOrigin::TyFn,
        );

        // Add all the locations to the args:
        self.copy_location_from_nodes_to_targets(node.args.ast_ref_iter(), args);

        // Create the type function call term:
        let app_ty_fn_term = self.builder().create_app_ty_fn_term(subject, args);

        self.validate_and_register_simplified_term(node, app_ty_fn_term)
    }

    type NamedTyRet = TermId;

    fn visit_named_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        let walk::NamedTy { name } = walk::walk_named_ty(self, ctx, node)?;

        // Infer type if it is an underscore:
        let term = if name == CORE_IDENTIFIERS.underscore {
            self.builder().create_unresolved_term()
        } else {
            self.builder().create_var_term(name)
        };

        self.validate_and_register_simplified_term(node, term)
    }

    type AccessTyRet = TermId;

    fn visit_access_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        let walk::AccessTy { subject, property } = walk::walk_access_ty(self, ctx, node)?;
        let term = self.builder().create_access(subject, property, AccessOp::Namespace);
        self.validate_and_register_simplified_term(node, term)
    }

    type RefTyRet = TermId;

    fn visit_ref_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::RefTy>,
    ) -> Result<Self::RefTyRet, Self::Error> {
        let walk::RefTy { inner, mutability, kind } = walk::walk_ref_ty(self, ctx, node)?;

        // Either mutable or immutable, raw or normal, depending on what was given:
        let ref_def = match (kind, mutability) {
            // Immutable, normal, by default:
            (Some(RefKind::Normal) | None, None | Some(Mutability::Immutable)) => {
                self.core_defs().reference_ty_fn()
            }
            (Some(RefKind::Raw), None | Some(Mutability::Immutable)) => {
                self.core_defs().raw_reference_ty_fn()
            }
            (Some(RefKind::Normal) | None, Some(Mutability::Mutable)) => {
                self.core_defs().reference_mut_ty_fn()
            }
            (Some(RefKind::Raw), Some(Mutability::Mutable)) => {
                self.core_defs().raw_reference_mut_ty_fn()
            }
        };
        let builder = self.builder();
        let ref_args = builder.create_args([builder.create_arg("T", inner)], ParamOrigin::TyFn);
        let ref_ty = builder.create_app_ty_fn_term(ref_def, ref_args);

        // Add locations:
        self.copy_location_from_node_to_target(node.inner.ast_ref(), (ref_args, 0));

        self.validate_and_register_simplified_term(node, ref_ty)
    }

    type MergeTyRet = TermId;

    fn visit_merge_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MergeTy>,
    ) -> Result<Self::MergeTyRet, Self::Error> {
        let walk::MergeTy { lhs, rhs } = walk::walk_merge_ty(self, ctx, node)?;
        let merge_term = self.builder().create_merge_term(vec![lhs, rhs]);
        self.validate_and_register_simplified_term(node, merge_term)
    }

    type UnionTyRet = TermId;
    fn visit_union_ty(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnionTy>,
    ) -> Result<Self::UnionTyRet, Self::Error> {
        let walk::UnionTy { lhs, rhs } = walk::walk_union_ty(self, ctx, node)?;
        let union_term = self.builder().create_union_term(vec![lhs, rhs]);
        self.validate_and_register_simplified_term(node, union_term)
    }

    type TyFnDefRet = TermId;

    fn visit_ty_fn_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let declaration_hint = self.state.declaration_name_hint.take();

        // Traverse the parameters:
        let param_elements = Self::try_collect_items(
            ctx,
            node.params.iter().map(|t| self.visit_param(ctx, t.ast_ref())),
        )?;
        let params = self.builder().create_params(param_elements, ParamOrigin::TyFn);

        // Add all the locations to the parameters:
        self.copy_location_from_nodes_to_targets(node.params.ast_ref_iter(), params);

        // Enter parameter scope:
        let param_scope = self.scope_manager().make_bound_scope(params);
        ScopeManager::enter_scope_with(self, param_scope, |this| {
            // Traverse return type and return value:
            let return_ty =
                node.return_ty.as_ref().map(|t| this.visit_ty(ctx, t.ast_ref())).transpose()?;
            let body = this.visit_expr(ctx, node.body.ast_ref())?;

            // Create the type function type term:
            let ty_fn_return_ty = this.builder().or_unresolved_term(return_ty);
            let ty_of_ty_fn_return_value = this.typer().infer_ty_of_term(body)?;
            let return_ty_sub =
                this.unifier().unify_terms(ty_of_ty_fn_return_value, ty_fn_return_ty)?;
            let ty_fn_return_ty =
                this.substituter().apply_sub_to_term(&return_ty_sub, ty_fn_return_ty);
            let ty_fn_return_value = this.substituter().apply_sub_to_term(&return_ty_sub, body);

            let ty_fn_term = this.builder().create_ty_fn_term(
                declaration_hint,
                params,
                ty_fn_return_ty,
                ty_fn_return_value,
            );

            this.validate_and_register_simplified_term(node, ty_fn_term)
        })
    }

    type FnDefRet = TermId;

    fn visit_fn_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        let params: Vec<_> = node
            .params
            .iter()
            .map(|a| self.visit_param(ctx, a.ast_ref()))
            .collect::<TcResult<_>>()?;

        let return_ty =
            node.return_ty.as_ref().map(|t| self.visit_ty(ctx, t.ast_ref())).transpose()?;

        // Set return type to hint if given
        let old_return_ty = mem::replace(&mut self.state.fn_def_return_ty, return_ty);
        let params_potentially_unresolved = self.builder().create_params(params, ParamOrigin::Fn);
        let param_scope = self.scope_manager().make_rt_param_scope(params_potentially_unresolved);

        let (params, return_ty, return_value) =
            ScopeManager::enter_scope_with(self, param_scope, |this| {
                let fn_body = this.visit_expr(ctx, node.fn_body.ast_ref())?;

                let hint_return_ty = this.state.fn_def_return_ty;
                let return_ty_or_unresolved = this.builder().or_unresolved_term(hint_return_ty);

                let body_sub = {
                    let ty_of_body = this.typer().infer_ty_of_term(fn_body)?;
                    match hint_return_ty {
                        Some(_) => {
                            // Try to unify ty_of_body with void, and if so, then ty of
                            // body should be unresolved:
                            let void = this.builder().create_void_ty_term();
                            match this.unifier().unify_terms(ty_of_body, void) {
                                Ok(_) => Sub::empty(),
                                Err(_) => {
                                    // Must be returning the same type:
                                    this.unifier()
                                        .unify_terms(ty_of_body, return_ty_or_unresolved)?
                                }
                            }
                        }
                        None => this.unifier().unify_terms(ty_of_body, return_ty_or_unresolved)?,
                    }
                };

                let return_value = this.substituter().apply_sub_to_term(&body_sub, fn_body);
                let return_ty =
                    this.substituter().apply_sub_to_term(&body_sub, return_ty_or_unresolved);
                let params = this
                    .substituter()
                    .apply_sub_to_params(&body_sub, params_potentially_unresolved);

                // Add all the locations to the parameters
                this.copy_location_from_nodes_to_targets(node.params.ast_ref_iter(), params);

                Ok((params, return_ty, return_value))
            })?;

        let builder = self.builder();

        let fn_ty_term =
            builder.create_fn_lit_term(builder.create_fn_ty_term(params, return_ty), return_value);

        // Clear return type
        self.state.fn_def_return_ty = old_return_ty;

        self.validate_and_register_simplified_term(node, fn_ty_term)
    }

    type ParamRet = Param;
    fn visit_param(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error> {
        match node.origin {
            ast::ParamOrigin::Struct | ast::ParamOrigin::Fn | ast::ParamOrigin::EnumVariant => {
                self.visit_fn_or_struct_param(node, ctx)
            }
            ast::ParamOrigin::TyFn => self.visit_ty_fn_param(node, ctx),
            // Any other `origin` does not occur within `Param`
            _ => unreachable!(),
        }
    }

    type BlockRet = TermId;

    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        walk::walk_block_same_children(self, ctx, node)
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &mut self,
        _: &Self::Ctx,
        _: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        // Handled in match
        Ok(())
    }

    type MatchBlockRet = TermId;

    fn visit_match_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let walk::MatchBlock { subject, .. } = walk::walk_match_block(self, ctx, node)?;

        let mut branches = vec![];

        let match_return_values: Vec<_> = node
            .cases
            .ast_ref_iter()
            .map(|case| {
                // Try to match the pattern with the case
                let case_pat = self.visit_pat(ctx, case.pat.ast_ref())?;
                branches.push(case_pat);

                let case_match = self.pat_matcher().match_pat_with_term(case_pat, subject)?;
                match case_match {
                    Some(members_to_add) => {
                        // Enter a new scope and add the members
                        let match_case_scope =
                            self.builder().create_scope(ScopeKind::Variable, members_to_add);
                        ScopeManager::enter_scope_with(self, match_case_scope, |this| {
                            // Traverse the body with the bound variables:
                            let case_body = this.visit_expr(ctx, case.expr.ast_ref())?;
                            Ok(Some(case_body))
                        })
                    }
                    None => {
                        // Emit warning for the useless match case in the event that the pattern
                        // will never match with the subject since we know the types will never
                        // correspond.
                        self.diagnostics()
                            .add_warning(TcWarning::UselessMatchCase { pat: case_pat, subject });

                        Ok(None)
                    }
                }
            })
            .flatten_ok()
            .collect::<TcResult<_>>()?;

        let ty_of_subject = self.typer().infer_ty_of_term(subject)?;

        // Skip origins of `while` and `if` since they are always irrefutable, if the
        // origin is a match, we want to check call `is_match_exhaustive` since it will
        // generate a more relevant error, otherwise we call `is_pat_irrefutable`
        match &node.body().origin {
            MatchOrigin::If | MatchOrigin::While => {}
            MatchOrigin::Match => {
                self.exhaustiveness_checker().is_match_exhaustive(&branches, subject)?
            }
            origin @ MatchOrigin::For => self.exhaustiveness_checker().is_pat_irrefutable(
                &branches,
                ty_of_subject,
                Some(*origin),
            )?,
        }

        let match_return_types: Vec<_> = match_return_values
            .iter()
            .copied()
            .map(|value| self.typer().infer_ty_of_term(value))
            .collect::<TcResult<_>>()?;
        let return_ty = self.builder().create_union_term(match_return_types);
        let return_term = self.builder().create_rt_term(return_ty);

        self.validate_and_register_simplified_term(node, return_term)
    }

    type LoopBlockRet = TermId;

    fn visit_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let walk::LoopBlock(_) = walk::walk_loop_block(self, ctx, node)?;
        let void_term = self.builder().create_void_term();
        self.validate_and_register_simplified_term(node, void_term)
    }

    type ForLoopBlockRet = TermId;

    fn visit_for_loop_block(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        panic_on_span!(
            self.source_location_at_node(node),
            self.source_map(),
            "hit non de-sugared for-block whilst performing typechecking"
        );
    }

    type WhileLoopBlockRet = TermId;

    fn visit_while_loop_block(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        panic_on_span!(
            self.source_location_at_node(node),
            self.source_map(),
            "hit non de-sugared while-block whilst performing typechecking"
        );
    }

    type ModBlockRet = TermId;

    fn visit_mod_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        // create a scope for the module definition
        let VisitConstantScope { scope_name, scope_id, .. } =
            self.visit_constant_scope(ctx, node.0.members(), None)?;

        // @@Todo: bound variables
        let mod_def = self.builder().create_mod_def(scope_name, ModDefOrigin::Mod, scope_id);
        let term = self.builder().create_mod_def_term(mod_def);

        // Validate the definition
        let is_within_intrinsics = self.state.within_intrinsics_directive;
        self.validator().validate_mod_def(mod_def, term, is_within_intrinsics)?;

        self.register_node_info(node, term);
        Ok(term)
    }

    type ImplBlockRet = TermId;

    fn visit_impl_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        // create a scope for the module definition
        let VisitConstantScope { scope_name, scope_id, .. } =
            self.visit_constant_scope(ctx, node.0.members(), None)?;

        // @@Todo: bound variables
        let mod_def = self.builder().create_mod_def(scope_name, ModDefOrigin::AnonImpl, scope_id);
        let term = self.builder().create_mod_def_term(mod_def);

        // Validate the definition
        self.validator().validate_mod_def(mod_def, term, false)?;

        self.register_node_info(node, term);
        Ok(term)
    }

    type IfClauseRet = TermId;

    fn visit_if_clause(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        panic_on_span!(
            self.source_location_at_node(node),
            self.source_map(),
            "hit non de-sugared if-clause whilst performing typechecking"
        );
    }

    type IfBlockRet = TermId;

    fn visit_if_block(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        panic_on_span!(
            self.source_location_at_node(node),
            self.source_map(),
            "hit non de-sugared if-block whilst performing typechecking"
        );
    }

    type BodyBlockRet = TermId;

    fn visit_body_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        // Traverse each statement
        for statement in node.statements.iter() {
            let statement_id = self.visit_expr(ctx, statement.ast_ref())?;
            self.validator().validate_term(statement_id)?;
            // @@Design: do we check that the return type is void? Should we
            // warn if it isn't?
        }

        // Traverse the ending expression, if any, or return void.
        let term = match &node.expr {
            Some(expr) => self.visit_expr(ctx, expr.ast_ref())?,
            None => self.builder().create_void_term(),
        };
        self.validate_and_register_simplified_term(node, term)
    }

    type ReturnStatementRet = TermId;

    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        let walk::ReturnStatement(return_term) = walk::walk_return_statement(self, ctx, node)?;

        // Add the given return value's type to the return type hint.
        // Return term is either given or void.
        let return_term = return_term.unwrap_or_else(|| {
            let builder = self.builder();
            let term = builder.create_void_term();
            self.copy_location_from_node_to_target(node, term);
            term
        });

        let return_ty = self.typer().infer_ty_of_term(return_term)?;
        let already_given_return_ty =
            self.state.fn_def_return_ty.unwrap_or_else(|| self.builder().create_unresolved_term());

        let return_ty_sub = self.unifier().unify_terms(return_ty, already_given_return_ty)?;
        let unified_return_ty =
            self.substituter().apply_sub_to_term(&return_ty_sub, already_given_return_ty);
        let _ = self.state.fn_def_return_ty.insert(unified_return_ty);

        // Return never as the return expression shouldn't evaluate to anything.
        let never_term = self.builder().create_never_ty();
        let term = self.builder().create_rt_term(never_term);

        self.validate_and_register_simplified_term(node, term)
    }

    type BreakStatementRet = TermId;

    fn visit_break_statement(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        let builder = self.builder();
        let term = builder.create_void_term();
        self.validate_and_register_simplified_term(node, term)
    }

    type ContinueStatementRet = TermId;
    fn visit_continue_statement(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        let builder = self.builder();
        let term = builder.create_void_term();
        self.validate_and_register_simplified_term(node, term)
    }

    type VisibilityRet = Visibility;

    fn visit_visibility_modifier(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error> {
        Ok(match node.body() {
            hash_ast::ast::Visibility::Public => Visibility::Public,
            hash_ast::ast::Visibility::Private => Visibility::Private,
        })
    }

    type MutabilityRet = Mutability;

    fn visit_mutability_modifier(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error> {
        Ok(match node.body() {
            hash_ast::ast::Mutability::Mutable => Mutability::Mutable,
            hash_ast::ast::Mutability::Immutable => Mutability::Immutable,
        })
    }

    type RefKindRet = RefKind;

    fn visit_ref_kind(
        &mut self,
        _: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<RefKind>,
    ) -> Result<Self::RefKindRet, Self::Error> {
        Ok(*node.body())
    }

    type DeclarationRet = TermId;
    fn visit_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let pat_id = self.visit_pat(ctx, node.pat.ast_ref())?;
        let pat = self.reader().get_pat(pat_id);

        // Set the declaration hit if it is just a binding pattern:
        if let Pat::Binding(BindingPat { name, .. }) = pat {
            self.state.declaration_name_hint = Some(name);
        };

        let ty = node.ty.as_ref().map(|t| self.visit_ty(ctx, t.ast_ref())).transpose()?;
        let value = node.value.as_ref().map(|t| self.visit_expr(ctx, t.ast_ref())).transpose()?;

        // Clear the declaration hint
        self.state.declaration_name_hint.take();

        let ty_or_unresolved = self.builder().or_unresolved_term(ty);

        // Unify the type of the declaration with the type of the value of the
        // declaration.
        let sub = if let Some(value) = value {
            let ty_of_value = self.typer().infer_ty_of_term(value)?;
            self.unifier().unify_terms(ty_of_value, ty_or_unresolved)?
        } else {
            Sub::empty()
        };

        // Apply the substitution on the type and value
        let mut value = value.map(|value| self.substituter().apply_sub_to_term(&sub, value));
        let ty = self.substituter().apply_sub_to_term(&sub, ty_or_unresolved);

        if value.is_none() && self.state.within_intrinsics_directive {
            // @@Todo: see #391
            value = Some(self.builder().create_rt_term(ty));
        }

        // Get the declaration member(s)
        let members = match value {
            Some(value) => {
                // If there is a value, match it with the pattern and acquire the members to add
                // to the scope.
                let members = match self.pat_matcher().match_pat_with_term(pat_id, value)? {
                    Some(members) => members,

                    None => {
                        self.diagnostics().add_warning(TcWarning::UselessMatchCase {
                            pat: pat_id,
                            subject: value,
                        });
                        vec![]
                    }
                };

                // Ensure that the given pattern is irrefutable given the type of the term
                self.exhaustiveness_checker().is_pat_irrefutable(&[pat_id], ty, None)?;
                members
            }
            None => {
                if let Pat::Binding(BindingPat { name, mutability: _, visibility }) = pat {
                    // Add the member without a value:

                    // @@Todo: differentiate between different kinds of members more appropriately:
                    vec![Member::uninitialised_constant(
                        name, visibility, // mutability,
                        ty,
                    )]
                } else {
                    // If there is no value, one cannot use pattern matching!
                    return Err(TcError::CannotPatMatchWithoutAssignment { pat: pat_id });
                }
            }
        };

        // Add the members to scope:
        let current_scope_id = self.scopes().current_scope();
        let member_indexes = members
            .iter()
            .map(|member| {
                self.scope_store().modify_fast(current_scope_id, |scope| scope.add(*member))
            })
            .collect::<Vec<_>>();

        // Add the locations of all members:
        for member_idx in &member_indexes {
            let member_span = iter::once(node.pat.span())
                .chain(node.ty.as_ref().map(|ty| ty.span()))
                .chain(node.value.as_ref().map(|value| value.span()))
                .reduce(|acc, span| acc.join(span))
                .unwrap();

            self.location_store().add_location_to_target(
                (current_scope_id, *member_idx),
                self.source_location(member_span),
            );
        }

        // Declaration should return its value if any:
        let term = match value {
            Some(value) => value,
            // Void if no value:
            None => self.builder().create_void_term(),
        };

        self.validate_and_register_simplified_term(node, term)
    }

    type MergeDeclarationRet = TermId;

    fn visit_merge_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        let walk::MergeDeclaration { decl, value } = walk::walk_merge_declaration(self, ctx, node)?;

        let merge_term = self.builder().create_merge_term(vec![decl, value]);

        // Add location
        self.copy_location_from_node_to_target(node, merge_term);
        Ok(self.validator().validate_term(merge_term)?.simplified_term_id)
    }

    type AssignExprRet = TermId;

    fn visit_assign_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignExpr>,
    ) -> Result<Self::AssignExprRet, Self::Error> {
        let rhs = self.visit_expr(ctx, node.rhs.ast_ref())?;

        // Try to resolve the variable in scopes; if it is not found, it is an error. If
        // it is found, then set it to its new term.
        let name = match node.lhs.kind() {
            ast::ExprKind::Variable(name) => name.name.ident,
            _ => {
                return Err(TcError::InvalidAssignSubject {
                    location: self.source_location_at_node(node).into(),
                });
            }
        };
        let var_term = self.builder().create_var_term(name);
        self.copy_location_from_node_to_target(node, var_term);
        let member = self.scope_manager().resolve_name_in_scopes(name, var_term)?;

        // Set the value to the member:
        self.scope_manager().assign_member(member.scope_id, member.index, rhs)?;

        let term = self.builder().create_void_term();
        self.validate_and_register_simplified_term(node, term)
    }

    type AssignOpExprRet = TermId;

    fn visit_assign_op_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignOpExpr>,
    ) -> Result<Self::AssignOpExprRet, Self::Error> {
        todo!()
    }

    type BinaryExprRet = TermId;

    fn visit_binary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BinaryExpr>,
    ) -> Result<Self::BinaryExprRet, Self::Error> {
        let walk::BinaryExpr { lhs, rhs, .. } = walk::walk_binary_expr(self, ctx, node)?;

        let operator_fn = |trait_fn_name: &str| {
            let prop_access = self.builder().create_prop_access(lhs, trait_fn_name);
            self.copy_location_from_node_to_target(node.operator.ast_ref(), prop_access);

            let builder = self.builder();
            builder.create_fn_call_term(
                prop_access,
                builder.create_args([builder.create_nameless_arg(rhs)], ParamOrigin::Fn),
            )
        };

        let lazy_operator_fn = |visitor: &mut Self, trait_name: &str| -> TcResult<TermId> {
            let lhs_ty = visitor.typer().infer_ty_of_term(lhs)?;
            let rhs_ty = visitor.typer().infer_ty_of_term(rhs)?;

            let builder = visitor.builder();

            // () => lhs
            let fn_ty =
                builder.create_fn_ty_term(builder.create_params([], ParamOrigin::Fn), lhs_ty);
            let lhs = builder.create_fn_lit_term(fn_ty, lhs);

            // () => rhs
            let fn_ty =
                builder.create_fn_ty_term(builder.create_params([], ParamOrigin::Fn), rhs_ty);
            let rhs = builder.create_fn_lit_term(fn_ty, rhs);

            // (() => lhs).trait_name()
            let prop_access = builder.create_prop_access(lhs, trait_name);

            // (() => lhs).trait_name(() => rhs)
            Ok(builder.create_fn_call_term(
                prop_access,
                builder.create_args([builder.create_nameless_arg(rhs)], ParamOrigin::Fn),
            ))
        };

        let term = match node.operator.body() {
            BinOp::Merge => self.builder().create_merge_term([lhs, rhs]),
            BinOp::As => unreachable!(),
            BinOp::EqEq => operator_fn("eq"),
            BinOp::NotEq => operator_fn("not_eq"),
            BinOp::BitOr => operator_fn("bit_or"),
            BinOp::Or => operator_fn("or"),
            BinOp::BitAnd => operator_fn("bit_and"),
            BinOp::And => operator_fn("and"),
            BinOp::BitXor => operator_fn("bit_xor"),
            BinOp::Exp => operator_fn("exp"),
            BinOp::Shr => operator_fn("bit_shr"),
            BinOp::Shl => operator_fn("bit_shl"),
            BinOp::Add => operator_fn("add"),
            BinOp::Sub => operator_fn("sub"),
            BinOp::Mul => operator_fn("mul"),
            BinOp::Div => operator_fn("div"),
            BinOp::Mod => operator_fn("modulo"),
            BinOp::Gt => lazy_operator_fn(self, "gt")?,
            BinOp::GtEq => lazy_operator_fn(self, "gt_eq")?,
            BinOp::Lt => lazy_operator_fn(self, "lt")?,
            BinOp::LtEq => lazy_operator_fn(self, "lt_eq")?,
        };

        self.validate_and_register_simplified_term(node, term)
    }

    type UnaryExprRet = TermId;

    fn visit_unary_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnaryExpr>,
    ) -> Result<Self::UnaryExprRet, Self::Error> {
        let walk::UnaryExpr { expr, .. } = walk::walk_unary_expr(self, ctx, node)?;

        let operator_fn = |trait_fn_name: &str| {
            let prop_access = self.builder().create_prop_access(expr, trait_fn_name);
            self.copy_location_from_node_to_target(node.operator.ast_ref(), prop_access);

            let builder = self.builder();
            builder.create_fn_call_term(prop_access, builder.create_args([], ParamOrigin::Fn))
        };

        // Convert the unary operator into a method call on the `expr`
        let term = match node.operator.body() {
            UnOp::BitNot => operator_fn("bit_not"),
            UnOp::Not => operator_fn("not"),
            UnOp::Neg => operator_fn("neg"),
        };

        self.validate_and_register_simplified_term(node, term)
    }

    type IndexExprRet = TermId;

    fn visit_index_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IndexExpr>,
    ) -> Result<Self::IndexExprRet, Self::Error> {
        let walk::IndexExpr { index_expr, subject } = walk::walk_index_expr(self, ctx, node)?;

        // We just translate this to a function call:
        let builder = self.builder();
        let index_fn_call_args =
            builder.create_args([builder.create_nameless_arg(index_expr)], ParamOrigin::Fn);
        let index_fn_call_subject = builder.create_prop_access(subject, "index");
        let index_fn_call = builder.create_fn_call_term(index_fn_call_subject, index_fn_call_args);

        // Add locations:
        self.copy_location_from_node_to_target(node, index_fn_call);
        self.copy_location_from_node_to_target(node.subject.ast_ref(), index_fn_call_subject);
        self.copy_location_from_node_to_target(node.index_expr.ast_ref(), (index_fn_call_args, 0));

        // @@ErrorReporting: We could provide customised error reporting here.
        self.validate_and_register_simplified_term(node, index_fn_call)
    }

    type StructDefRet = TermId;

    fn visit_struct_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let walk::StructDef { entries } = walk::walk_struct_def(self, ctx, node)?;

        // create the params
        let fields = self.builder().create_params(entries, ParamOrigin::Struct);

        // add the location of each parameter
        self.copy_location_from_nodes_to_targets(node.fields.ast_ref_iter(), fields);

        // take the declaration hint here...
        let name = self.state.declaration_name_hint.take();

        let builder = self.builder();
        let nominal_id = builder.create_struct_def(name, fields);
        let term = builder.create_nominal_def_term(nominal_id);

        // validate the constructed nominal def
        self.validator().validate_nominal_def(nominal_id)?;

        self.register_node_info(node, term);
        Ok(term)
    }

    type EnumDefEntryRet = (Identifier, NominalDefId);

    fn visit_enum_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        let walk::EnumDefEntry { name, fields } = walk::walk_enum_def_entry(self, ctx, node)?;

        // Create the enum variant parameters
        if fields.is_empty() {
            // This is a unit variant:
            Ok((name, self.builder().create_named_unit_def(name)))
        } else {
            // This is a struct variant:
            Ok((
                name,
                self.builder().create_named_struct_def(
                    name,
                    self.builder().create_params(
                        fields.iter().map(|field| Param {
                            name: field.name,
                            ty: field.ty,
                            default_value: None,
                        }),
                        ParamOrigin::EnumVariant,
                    ),
                ),
            ))
        }
    }

    type EnumDefRet = TermId;

    fn visit_enum_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let walk::EnumDef { entries } = walk::walk_enum_def(self, ctx, node)?;

        let builder = self.builder();
        let enum_variant_union = builder.create_union_term(
            entries.iter().map(|(_, entry)| builder.create_nominal_def_term(*entry)),
        );

        self.validate_and_register_simplified_term(node, enum_variant_union)
    }

    type TraitDefRet = TermId;

    fn visit_trait_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        // create a scope for the module definition
        let VisitConstantScope { scope_name, scope_id, .. } =
            self.visit_constant_scope(ctx, node.members.ast_ref_iter(), None)?;

        // @@Todo: bound variables
        let trt_def = self.builder().create_trt_def(scope_name, scope_id);
        let term = self.builder().create_trt_term(trt_def);

        // Validate the definition
        self.validator().validate_trt_def(trt_def)?;

        self.register_node_info(node, term);
        Ok(term)
    }

    type TraitImplRet = TermId;

    fn visit_trait_impl(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        let trt_term = self.visit_ty(ctx, node.ty.ast_ref())?;

        // create a scope for the module definition
        let VisitConstantScope { scope_name, scope_id, .. } =
            self.visit_constant_scope(ctx, node.implementation.ast_ref_iter(), None)?;

        // @@Todo: bound variables
        let mod_def =
            self.builder().create_mod_def(scope_name, ModDefOrigin::TrtImpl(trt_term), scope_id);
        let term = self.builder().create_mod_def_term(mod_def);

        // Validate the definition
        self.register_node_info(node.ty.ast_ref(), term);
        self.validator().validate_mod_def(mod_def, term, false)?;

        Ok(term)
    }

    type PatRet = PatId;

    fn visit_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Pat>,
    ) -> Result<Self::PatRet, Self::Error> {
        walk::walk_pat_same_children(self, ctx, node)
    }

    type AccessPatRet = PatId;

    fn visit_access_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        let walk::AccessPat { subject, property } = walk::walk_access_pat(self, ctx, node)?;
        let access_pat = self.builder().create_access_pat(subject, property);
        self.register_node_info(node, access_pat);
        Ok(access_pat)
    }

    type ConstructorPatRet = PatId;

    fn visit_constructor_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        let walk::ConstructorPat { args, subject } = walk::walk_constructor_pat(self, ctx, node)?;

        let constructor_params = self.builder().create_pat_args(args, ParamOrigin::ConstructorPat);
        self.copy_location_from_nodes_to_targets(node.fields.ast_ref_iter(), constructor_params);

        let subject = self.typer().get_term_of_pat(subject)?;
        let simplified = self.simplifier().potentially_simplify_term(subject)?;

        let constructor_pat = self.builder().create_constructor_pat(simplified, constructor_params);

        self.copy_location_from_node_to_target(node, constructor_pat);
        self.validator().validate_constructor_pat(constructor_pat)?;
        self.register_node_info(node, constructor_pat);
        Ok(constructor_pat)
    }

    type TuplePatEntryRet = PatArg;

    fn visit_tuple_pat_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePatEntry>,
    ) -> Result<Self::TuplePatEntryRet, Self::Error> {
        // Here we set the `in_pat_fields` as true since we're currently within
        // some kind of pattern fields...
        let walk::TuplePatEntry { name, pat } = walk::walk_tuple_pat_entry(self, ctx, node)?;

        Ok(PatArg { name, pat })
    }

    type TuplePatRet = PatId;

    fn visit_tuple_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        let walk::TuplePat { elements } = walk::walk_tuple_pat(self, ctx, node)?;

        let members = self.builder().create_pat_args(elements, ParamOrigin::Tuple);
        self.copy_location_from_nodes_to_targets(node.fields.ast_ref_iter(), members);
        let tuple_pat = self.builder().create_tuple_pat(members);

        self.copy_location_from_node_to_target(node, tuple_pat);
        self.validator().validate_tuple_pat(members)?;
        self.register_node_info(node, tuple_pat);
        Ok(tuple_pat)
    }

    type ListPatRet = PatId;

    fn visit_list_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListPat>,
    ) -> Result<Self::ListPatRet, Self::Error> {
        let walk::ListPat { elements } = walk::walk_list_pat(self, ctx, node)?;

        // We need to collect all of the terms within the inner pattern, but we need
        // have a special case for `spread patterns` because they will return `[term]`
        // rather than `term`...
        let inner_terms = elements
            .iter()
            .zip(node.fields.iter())
            .filter(|(_, node)| !matches!(node.body(), hash_ast::ast::Pat::Spread(_)))
            .map(|(element, _)| -> TcResult<TermId> { self.typer().get_term_of_pat(*element) })
            .collect::<TcResult<Vec<_>>>()?;

        let list_term = self.unifier().unify_rt_term_sequence(inner_terms)?;

        let members = self.builder().create_pat_args(
            elements.into_iter().map(|pat| PatArg { name: None, pat }),
            ParamOrigin::ListPat,
        );

        let list_pat = self.builder().create_list_pat(list_term, members);

        self.copy_location_from_nodes_to_targets(node.fields.ast_ref_iter(), members);

        self.register_node_info(node, list_pat);
        Ok(list_pat)
    }

    type SpreadPatRet = PatId;

    fn visit_spread_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::SpreadPat>,
    ) -> Result<Self::SpreadPatRet, Self::Error> {
        let walk::SpreadPat { name } = walk::walk_spread_pat(self, ctx, node)?;

        let spread_pat = self.builder().create_pat(Pat::Spread(SpreadPat { name }));

        self.register_node_info(node, spread_pat);
        Ok(spread_pat)
    }

    type LitPatRet = PatId;

    fn visit_lit_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::LitPat>,
    ) -> Result<Self::LitPatRet, Self::Error> {
        let walk::LitPat(lit) = walk::walk_lit_pat(self, ctx, node)?;

        let pat = match node.body().0.body() {
            Lit::Bool(_) => self.builder().create_constant_pat(lit),
            _ => self.builder().create_lit_pat(lit),
        };

        self.register_node_info(node, pat);
        Ok(pat)
    }

    type RangePatRet = PatId;

    fn visit_range_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RangePat>,
    ) -> Result<Self::RangePatRet, Self::Error> {
        let walk::RangePat { lo, hi } = walk::walk_range_pat(self, ctx, node)?;

        let range_pat = RangePat { lo, hi, end: node.body().end };
        let pat = self.builder().create_range_pat(range_pat);

        self.copy_location_from_node_to_target(node, pat);
        self.validator().validate_range_pat(&range_pat)?;
        self.register_node_info(node, pat);
        Ok(pat)
    }

    type OrPatRet = PatId;
    fn visit_or_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::OrPat>,
    ) -> Result<Self::OrPatRet, Self::Error> {
        let walk::OrPat { variants } = walk::walk_or_pat(self, ctx, node)?;
        let pat = self.builder().create_or_pat(variants);
        self.register_node_info(node, pat);
        Ok(pat)
    }

    type IfPatRet = PatId;

    fn visit_if_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfPat>,
    ) -> Result<Self::IfPatRet, Self::Error> {
        let walk::IfPat { condition, pat } = walk::walk_if_pat(self, ctx, node)?;
        let pat = self.builder().create_if_pat(pat, condition);
        self.register_node_info(node, pat);
        Ok(pat)
    }

    type BindingPatRet = PatId;

    fn visit_binding_pat(
        &mut self,
        _: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        let name = node.name.ident;
        let var_term = self.builder().create_var_term(name);

        if let Ok(scope_member) = self.scope_manager().resolve_name_in_scopes(name, var_term) {
            let term = scope_member.member.value_or_ty();
            let ty = scope_member.member.ty();

            // So this should only become a constant if we are a `enum` or `struct`
            // definition. Otherwise, we shadow the variable
            if self.oracle().term_is_struct_def(term) || self.oracle().term_is_enum_def(term) {
                self.location_store().copy_location(ty, var_term);
                let pat = self.builder().create_pat(Pat::Const(ConstPat { term: var_term }));

                self.register_node_info(node, pat);
                return Ok(pat);
            }
        }

        let pat = self.builder().create_binding_pat(
            node.name.body().ident,
            match node.mutability.as_ref().map(|x| *x.body()) {
                Some(hash_ast::ast::Mutability::Mutable) => Mutability::Mutable,
                Some(hash_ast::ast::Mutability::Immutable) | None => Mutability::Immutable,
            },
            match node.visibility.as_ref().map(|x| *x.body()) {
                Some(hash_ast::ast::Visibility::Private) | None => Visibility::Private,
                Some(hash_ast::ast::Visibility::Public) => Visibility::Public,
            },
        );

        self.register_node_info(node, pat);
        Ok(pat)
    }

    type WildPatRet = PatId;

    fn visit_wild_pat(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::WildPat>,
    ) -> Result<Self::WildPatRet, Self::Error> {
        let pat = self.builder().create_wildcard_pat();
        self.register_node_info(node, pat);
        Ok(pat)
    }

    type ModulePatEntryRet = PatArg;

    fn visit_module_pat_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error> {
        let walk::ModulePatEntry { name, pat } = walk::walk_module_pat_entry(self, ctx, node)?;
        Ok(self.builder().create_pat_arg(name, pat))
    }

    type ModulePatRet = PatId;

    fn visit_module_pat(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModulePat>,
    ) -> Result<Self::ModulePatRet, Self::Error> {
        let walk::ModulePat { fields } = walk::walk_module_pat(self, ctx, node)?;
        let members = self.builder().create_pat_args(fields, ParamOrigin::ModulePat);
        let module_pat = self.builder().create_mod_pat(members);
        self.copy_location_from_nodes_to_targets(node.fields.ast_ref_iter(), members);
        self.register_node_info(node, module_pat);
        Ok(module_pat)
    }

    type ModuleRet = TermId;

    fn visit_module(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let id = self.local_storage().current_source();

        // Decide on whether we are creating a new scope, or if we are going to use the
        // global scope. If we're within the `prelude` module, we need to append
        // all members into the global scope rather than creating a new scope
        let members = if let Some(ModuleKind::Prelude) = self.source_map().module_kind_by_id(id) {
            self.global_storage().root_scope
        } else {
            self.builder().create_scope(ScopeKind::Constant, vec![])
        };

        // Get the end of the filename for the module and use this as the name of the
        // module
        let name = self.source_map().source_name(id).to_owned();
        let VisitConstantScope { scope_id, .. } =
            self.visit_constant_scope(ctx, node.contents.ast_ref_iter(), Some(members))?;

        let mod_def = self.builder().create_named_mod_def(name, ModDefOrigin::Source(id), scope_id);

        let term = self.builder().create_mod_def_term(mod_def);
        self.copy_location_from_node_to_target(node, term);
        self.validator().validate_mod_def(mod_def, term, false)?;

        // Add location to the term
        self.register_node_info(node, term);
        Ok(term)
    }
}
