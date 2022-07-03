//! Contains functions to traverse the AST and add types to it, while checking
//! it for correctness.

use crate::{
    diagnostics::error::{TcError, TcResult},
    ops::{validate::TermValidation, AccessToOpsMut},
    storage::{
        location::LocationTarget,
        primitives::{
            Arg, Member, MemberData, Mutability, Param, ParamOrigin, Sub, TermId, Visibility,
        },
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};
use hash_ast::{
    ast::{OwnsAstNode, RefKind},
    visitor::{self, walk, AstVisitor},
};
use hash_pipeline::sources::{NodeMap, SourceRef};
use hash_reporting::macros::panic_on_span;
use hash_source::{
    identifier::Identifier,
    location::{SourceLocation, Span},
    SourceId,
};

mod sequence;

/// Traverses the AST and adds types to it, while checking it for correctness.
///
/// Contains typechecker state that is accessed while traversing.
pub struct TcVisitor<'gs, 'ls, 'cd, 'src> {
    pub storage: StorageRefMut<'gs, 'ls, 'cd, 'src>,
    pub source_id: SourceId,
    pub node_map: &'src NodeMap,
}

impl<'gs, 'ls, 'cd, 'src> AccessToStorage for TcVisitor<'gs, 'ls, 'cd, 'src> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd, 'src> AccessToStorageMut for TcVisitor<'gs, 'ls, 'cd, 'src> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 'src> TcVisitor<'gs, 'ls, 'cd, 'src> {
    /// Create a new [TcVisitor] with the given state, traversing the given
    /// source from [Sources].
    pub fn new_in_source(
        storage: StorageRefMut<'gs, 'ls, 'cd, 'src>,
        source_id: SourceId,
        node_map: &'src NodeMap,
    ) -> Self {
        TcVisitor { storage, source_id, node_map }
    }

    /// Visits the source passed in as an argument to [Self::new], and returns
    /// the term of the module that corresponds to the source.
    pub fn visit_source(&mut self) -> TcResult<TermId> {
        let source = self.node_map.get_source(self.source_id);
        match source {
            SourceRef::Interactive(interactive_source) => {
                self.visit_body_block(&(), interactive_source.node_ref())
            }
            SourceRef::Module(module_source) => self.visit_module(&(), module_source.node_ref()),
        }
    }

    /// Create a [SourceLocation] from a [Span]
    pub(crate) fn source_location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, source_id: self.source_id }
    }
}

/// Represents a kind of pattern, with information about it.
#[derive(Clone, Debug)]
pub enum PatternHint {
    Binding { name: Identifier },
}

/// Implementation of [visitor::AstVisitor] for [TcVisitor], to traverse the AST
/// and type it.
///
/// Notes:
/// - Terms derived from expressions are always validated, in order to ensure
///   they are correct. The same goes for types.
impl<'gs, 'ls, 'cd, 'src> visitor::AstVisitor for TcVisitor<'gs, 'ls, 'cd, 'src> {
    type Ctx = ();
    type CollectionContainer<T> = Vec<T>;

    fn try_collect_items<T, E, I: Iterator<Item = Result<T, E>>>(
        _: &Self::Ctx,
        items: I,
    ) -> Result<Self::CollectionContainer<T>, E> {
        items.collect()
    }

    type Error = TcError;

    type ImportRet = TermId;

    fn visit_import(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        todo!()
    }

    type NameRet = Identifier;

    fn visit_name(
        &mut self,
        _: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        Ok(node.ident)
    }

    type AccessNameRet = TermId;

    fn visit_access_name(
        &mut self,
        _: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::AccessName>,
    ) -> Result<Self::AccessNameRet, Self::Error> {
        // Accumulate all the names into an access term:
        let mut names = node.path.iter();

        let first_name = names.next().unwrap();
        let location = self.source_location(first_name.span());

        let builder = self.builder();
        let mut current_term = builder.create_var_term(*first_name.body());

        builder.add_location_to_target(current_term, location);

        for access_name in names {
            let name_location = self.source_location(access_name.span());
            let builder = self.builder();

            current_term = builder.create_ns_access(current_term, *access_name.body());
            builder.add_location_to_target(current_term, name_location);
        }
        Ok(current_term)
    }

    type LiteralRet = TermId;

    fn visit_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Literal>,
    ) -> Result<Self::LiteralRet, Self::Error> {
        walk::walk_literal_same_children(self, ctx, node)
    }

    type BinaryOperatorRet = TermId;

    fn visit_binary_operator(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BinOp>,
    ) -> Result<Self::BinaryOperatorRet, Self::Error> {
        todo!()
    }

    type UnaryOperatorRet = TermId;

    fn visit_unary_operator(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnOp>,
    ) -> Result<Self::UnaryOperatorRet, Self::Error> {
        todo!()
    }

    type ExpressionRet = TermId;

    fn visit_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Expression>,
    ) -> Result<Self::ExpressionRet, Self::Error> {
        walk::walk_expression_same_children(self, ctx, node)
    }

    type VariableExprRet = TermId;

    fn visit_variable_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::VariableExpr>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        let walk::VariableExpr { name, .. } = walk::walk_variable_expr(self, ctx, node)?;

        // We need to add the location to the term
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(name, location);

        let TermValidation { simplified_term_id, .. } = self.validator().validate_term(name)?;
        Ok(simplified_term_id)
    }

    type DirectiveExprRet = TermId;

    fn visit_directive_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        // @@Directives: Decide on what to do with directives, but for now walk the
        // inner types...
        let walk::DirectiveExpr { subject, .. } = walk::walk_directive_expr(self, ctx, node)?;

        Ok(subject)
    }

    type ConstructorCallArgRet = TermId;

    fn visit_constructor_call_arg(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error> {
        todo!()
    }

    type ConstructorCallArgsRet = TermId;

    fn visit_constructor_call_args(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallArgs>,
    ) -> Result<Self::ConstructorCallArgsRet, Self::Error> {
        todo!()
    }

    type ConstructorCallExprRet = TermId;

    fn visit_constructor_call_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        todo!()
    }

    type PropertyAccessExprRet = TermId;

    fn visit_property_access_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::PropertyAccessExpr>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error> {
        todo!()
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
            self.core_defs().reference_mut_ty_fn
        } else {
            self.core_defs().reference_ty_fn
        };

        let builder = self.builder();

        // Create either `RefMut<T>` or `Ref<T>`
        let ref_args =
            builder.create_args([builder.create_arg("T", inner_expr)], ParamOrigin::TyFn);
        let ref_ty = builder.create_app_ty_fn_term(ref_def, ref_args);

        let term = builder.create_rt_term(ref_ty);

        // Add location to the type:
        let ref_expr_span = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, ref_expr_span);

        Ok(term)
    }

    type DerefExprRet = TermId;

    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let walk::DerefExpr(inner) = walk::walk_deref_expr(self, ctx, node)?;
        let inner_ty = self.typer().ty_of_term(inner)?;

        let ref_ty = self.core_defs().reference_ty_fn;
        let ap_ref_ty = {
            let builder = self.builder();

            builder.create_app_ty_fn_term(
                ref_ty,
                builder.create_args(
                    [builder.create_arg("T", builder.create_unresolved_term())],
                    ParamOrigin::TyFn,
                ),
            )
        };

        // Attempt to unify this with a `Ref<T>` to see if the `inner_ty` can
        // be dereferenced.
        // @@Todo: deal with `RefMut<T>` and raw references...
        let result = self.unifier().unify_terms(inner_ty, ap_ref_ty)?;

        // get the substitution result and use that as the return from the `inner_ty`
        let inner_ty = result.pairs().next().unwrap().1;

        let term = self.builder().create_rt_term(inner_ty);

        // Add the location to the type
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
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

    type LiteralExprRet = TermId;

    fn visit_literal_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::LiteralExpr>,
    ) -> Result<Self::LiteralExprRet, Self::Error> {
        Ok(walk::walk_literal_expr(self, ctx, node)?.0)
    }

    type CastExprRet = TermId;

    fn visit_cast_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        todo!()
    }

    type TypeExprRet = TermId;

    fn visit_type_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeExpr>,
    ) -> Result<Self::TypeExprRet, Self::Error> {
        Ok(walk::walk_type_expr(self, ctx, node)?.0)
    }

    type BlockExprRet = TermId;

    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BlockExpr>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        Ok(walk::walk_block_expr(self, ctx, node)?.0)
    }

    type ImportExprRet = TermId;

    fn visit_import_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        Ok(walk::walk_import_expr(self, ctx, node)?.0)
    }

    type TypeRet = TermId;

    fn visit_type(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Type>,
    ) -> Result<Self::TypeRet, Self::Error> {
        walk::walk_type_same_children(self, ctx, node)
    }

    type NamedFieldTypeRet = Param;

    fn visit_named_field_type(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::NamedFieldTypeEntry>,
    ) -> Result<Self::NamedFieldTypeRet, Self::Error> {
        let walk::NamedFieldTypeEntry { ty, name } = walk::walk_named_field_type(self, ctx, node)?;

        // Add the location of the type
        let location = self.source_location(node.ty.span());
        self.location_store_mut().add_location_to_target(ty, location);

        Ok(Param { ty, name, default_value: None })
    }

    type FnTypeRet = TermId;

    fn visit_function_type(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FnType>,
    ) -> Result<Self::FnTypeRet, Self::Error> {
        let walk::FnType { params, return_ty } = walk::walk_function_type(self, ctx, node)?;
        let params = self.builder().create_params(params, ParamOrigin::Fn);

        // Add all the locations to the parameters:
        for (index, param) in node.params.iter().enumerate() {
            let location = self.source_location(param.span());
            self.location_store_mut().add_location_to_target((params, index), location);
        }

        // Create the function type term:
        let fn_ty_term = self.builder().create_fn_ty_term(params, return_ty);

        // Add location to the type:
        let fn_ty_location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(fn_ty_term, fn_ty_location);

        Ok(self.validator().validate_term(fn_ty_term)?.simplified_term_id)
    }

    type TypeFunctionParamRet = Param;

    fn visit_type_function_param(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionParam>,
    ) -> Result<Self::TypeFunctionParamRet, Self::Error> {
        let walk::TypeFunctionParam { name, bound, default } =
            walk::walk_type_function_param(self, ctx, node)?;

        // The location of the param type is either the bound or the name (since <T>
        // means <T: Type>):
        let location = self.source_location(
            node.bound.as_ref().map(|bound| bound.span()).unwrap_or_else(|| node.name.span()),
        );
        // The type of the param is the given bound, or Type if no bound was given.
        let runtime_instantiable_trt = self.core_defs().runtime_instantiable_trt;
        let ty = bound.unwrap_or_else(|| self.builder().create_trt_term(runtime_instantiable_trt));
        self.location_store_mut().add_location_to_target(ty, location);

        Ok(Param { ty, name: Some(name), default_value: default })
    }

    type TypeFunctionRet = TermId;

    fn visit_type_function(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunction>,
    ) -> Result<Self::TypeFunctionRet, Self::Error> {
        let walk::TypeFunction { params: args, return_ty } =
            walk::walk_type_function(self, ctx, node)?;
        let params = self.builder().create_params(args, ParamOrigin::TyFn);

        // Add all the locations to the parameters:
        for (index, param) in node.params.iter().enumerate() {
            let location = self.source_location(param.span());
            self.location_store_mut().add_location_to_target((params, index), location);
        }

        // Create the type function type term:
        let ty_fn_ty_term = self.builder().create_ty_fn_ty_term(params, return_ty);

        // Add location to the type:
        let fn_ty_location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(ty_fn_ty_term, fn_ty_location);

        Ok(self.validator().validate_term(ty_fn_ty_term)?.simplified_term_id)
    }

    type TypeFunctionCallRet = TermId;

    fn visit_type_function_call(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionCall>,
    ) -> Result<Self::TypeFunctionCallRet, Self::Error> {
        let walk::TypeFunctionCall { args, subject } =
            walk::walk_type_function_call(self, ctx, node)?;

        // These should be converted to args
        let args = self.builder().create_args(
            args.iter().map(|param_arg| Arg { name: param_arg.name, value: param_arg.ty }),
            ParamOrigin::TyFn,
        );

        // Add all the locations to the args:
        for (index, entry) in node.body().args.iter().enumerate() {
            let location = self.source_location(entry.span());
            self.location_store_mut().add_location_to_target((args, index), location);
        }

        // Create the type function call term:
        let app_ty_fn_term = self.builder().create_app_ty_fn_term(subject, args);

        // Add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(app_ty_fn_term, location);

        Ok(self.validator().validate_term(app_ty_fn_term)?.simplified_term_id)
    }

    type NamedTypeRet = TermId;

    fn visit_named_type(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::NamedType>,
    ) -> Result<Self::NamedTypeRet, Self::Error> {
        if node.name.path.len() == 1 && *node.name.path[0].body() == Identifier::from("_") {
            // Infer type if it is an underscore:
            let infer_term = self.builder().create_unresolved_term();
            let infer_term_location = self.source_location(node.span());
            self.builder().add_location_to_target(infer_term, infer_term_location);
            Ok(infer_term)
        } else {
            let var = walk::walk_named_type(self, ctx, node)?.name;
            Ok(self.validator().validate_term(var)?.simplified_term_id)
        }
    }

    type RefTypeRet = TermId;

    fn visit_ref_type(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::RefType>,
    ) -> Result<Self::RefTypeRet, Self::Error> {
        let walk::RefType { inner, mutability, kind } = walk::walk_ref_type(self, ctx, node)?;

        // Either mutable or immutable, raw or normal, depending on what was given:
        let ref_def = match (kind, mutability) {
            // Immutable, normal, by default:
            (Some(RefKind::Normal) | None, None | Some(Mutability::Immutable)) => {
                self.core_defs().reference_ty_fn
            }
            (Some(RefKind::Raw), None | Some(Mutability::Immutable)) => {
                self.core_defs().raw_reference_ty_fn
            }
            (Some(RefKind::Normal) | None, Some(Mutability::Mutable)) => {
                self.core_defs().reference_mut_ty_fn
            }
            (Some(RefKind::Raw), Some(Mutability::Mutable)) => {
                self.core_defs().raw_reference_mut_ty_fn
            }
        };
        let ref_ty_location = self.source_location(node.span());
        let inner_ty_location = self.source_location(node.inner.span());
        let builder = self.builder();
        let ref_args = builder.create_args([builder.create_arg("T", inner)], ParamOrigin::TyFn);
        let ref_ty = builder.create_app_ty_fn_term(ref_def, ref_args);

        // Add locations:
        builder.add_location_to_target(ref_ty, ref_ty_location);
        builder.add_location_to_target(LocationTarget::Arg(ref_args, 0), inner_ty_location);

        Ok(self.validator().validate_term(ref_ty)?.simplified_term_id)
    }

    type MergedTypeRet = TermId;

    fn visit_merged_type(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MergedType>,
    ) -> Result<Self::MergedTypeRet, Self::Error> {
        let walk::MergedType(elements) = walk::walk_merged_type(self, ctx, node)?;

        let merge_term = self.builder().create_merge_term(elements);

        // Add location
        let merge_term_location = self.source_location(node.span());
        self.builder().add_location_to_target(merge_term, merge_term_location);

        Ok(self.validator().validate_term(merge_term)?.simplified_term_id)
    }

    type TypeFunctionDefRet = TermId;

    fn visit_type_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionDef>,
    ) -> Result<Self::TypeFunctionDefRet, Self::Error> {
        // Traverse the parameters:
        let param_elements = Self::try_collect_items(
            ctx,
            node.params.iter().map(|t| self.visit_type_function_def_param(ctx, t.ast_ref())),
        )?;
        let params = self.builder().create_params(param_elements, ParamOrigin::TyFn);

        // Add all the locations to the parameters:
        for (index, param) in node.params.iter().enumerate() {
            let location = self.source_location(param.span());
            self.location_store_mut().add_location_to_target((params, index), location);
        }

        // Enter parameter scope:
        let param_scope = self.scope_resolver().enter_ty_param_scope(params);

        // Traverse return type and return value:
        let return_ty =
            node.return_ty.as_ref().map(|t| self.visit_type(ctx, t.ast_ref())).transpose()?;
        let expression = self.visit_expression(ctx, node.expr.ast_ref())?;

        // Create the type function type term:
        let ty_fn_return_ty = self.builder().or_unresolved_term(return_ty);
        let ty_of_ty_fn_return_value = self.typer().ty_of_term(expression)?;
        let return_ty_sub =
            self.unifier().unify_terms(ty_of_ty_fn_return_value, ty_fn_return_ty)?;
        let ty_fn_return_ty = self.substituter().apply_sub_to_term(&return_ty_sub, ty_fn_return_ty);
        let ty_fn_return_value = self.substituter().apply_sub_to_term(&return_ty_sub, expression);

        let ty_fn_term =
            self.builder().create_nameless_ty_fn_term(params, ty_fn_return_ty, ty_fn_return_value);

        // Add location to the type function:
        let fn_ty_location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(ty_fn_term, fn_ty_location);

        let simplified_ty_fn_term = self.validator().validate_term(ty_fn_term)?.simplified_term_id;

        // Exit scope:
        self.scopes_mut().pop_the_scope(param_scope);

        Ok(simplified_ty_fn_term)
    }

    type TypeFunctionDefArgRet = Param;

    fn visit_type_function_def_param(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TypeFunctionDefParam>,
    ) -> Result<Self::TypeFunctionDefArgRet, Self::Error> {
        // @@Todo: default values
        let walk::TypeFunctionDefParam { name, ty, .. } =
            walk::walk_type_function_def_param(self, ctx, node)?;

        // The location of the param type is either the bound or the name (since <T>
        // means <T: Type>):
        let location = self.source_location(
            node.ty.as_ref().map(|bound| bound.span()).unwrap_or_else(|| node.name.span()),
        );
        // The type of the param is the given bound, or Type if no bound was given.
        let ty = ty.unwrap_or_else(|| self.builder().create_any_ty_term());
        self.location_store_mut().add_location_to_target(ty, location);

        Ok(Param { ty, name: Some(name), default_value: None })
    }

    type TupleTypeRet = TermId;

    fn visit_tuple_type(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleType>,
    ) -> Result<Self::TupleTypeRet, Self::Error> {
        let walk::TupleType { entries } = walk::walk_tuple_type(self, ctx, node)?;

        let members = self.builder().create_params(entries, ParamOrigin::Tuple);

        // We have to append locations to each of the parameters
        for (index, entry) in node.body().entries.iter().enumerate() {
            let location = self.source_location(entry.span());
            self.location_store_mut().add_location_to_target((members, index), location);
        }

        let builder = self.builder();
        let term = builder.create_tuple_ty_term(members);

        // Add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type ListTypeRet = TermId;

    fn visit_list_type(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListType>,
    ) -> Result<Self::ListTypeRet, Self::Error> {
        let walk::ListType { inner } = walk::walk_list_type(self, ctx, node)?;

        let inner_ty = self.core_defs().list_ty_fn;
        let builder = self.builder();

        let list_ty = builder.create_app_ty_fn_term(
            inner_ty,
            builder.create_args([builder.create_arg("T", inner)], ParamOrigin::TyFn),
        );

        let term = builder.create_rt_term(list_ty);

        // Add the location to the type
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type SetTypeRet = TermId;

    fn visit_set_type(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::SetType>,
    ) -> Result<Self::SetTypeRet, Self::Error> {
        let walk::SetType { inner } = walk::walk_set_type(self, ctx, node)?;

        let inner_ty = self.core_defs().set_ty_fn;
        let builder = self.builder();

        let set_ty = builder.create_app_ty_fn_term(
            inner_ty,
            builder.create_args([builder.create_arg("T", inner)], ParamOrigin::TyFn),
        );

        let term = builder.create_rt_term(set_ty);

        // Add the location to the type
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type MapTypeRet = TermId;

    fn visit_map_type(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapType>,
    ) -> Result<Self::MapTypeRet, Self::Error> {
        let walk::MapType { key, value } = walk::walk_map_type(self, ctx, node)?;

        let inner_ty = self.core_defs().map_ty_fn;
        let builder = self.builder();

        let map_ty = builder.create_app_ty_fn_term(
            inner_ty,
            builder.create_args(
                [builder.create_arg("K", key), builder.create_arg("V", value)],
                ParamOrigin::TyFn,
            ),
        );

        let term = builder.create_rt_term(map_ty);

        // Add the location to the type
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type MapLiteralRet = TermId;

    fn visit_map_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLiteral>,
    ) -> Result<Self::MapLiteralRet, Self::Error> {
        let walk::MapLiteral { entries } = walk::walk_map_literal(self, ctx, node)?;
        let map_inner_ty = self.core_defs().map_ty_fn;

        // Unify the key and value types...
        let key_ty = self.unify_term_sequence(entries.iter().map(|(k, _)| *k))?;
        let val_ty = self.unify_term_sequence(entries.iter().map(|(v, _)| *v))?;

        let builder = self.builder();
        let map_ty = builder.create_app_ty_fn_term(
            map_inner_ty,
            builder.create_args(
                [builder.create_arg("K", key_ty), builder.create_arg("V", val_ty)],
                ParamOrigin::TyFn,
            ),
        );

        let term = builder.create_rt_term(map_ty);

        // add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type MapLiteralEntryRet = (TermId, TermId);

    fn visit_map_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::MapLiteralEntry>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error> {
        let walk::MapLiteralEntry { key, value } = walk::walk_map_literal_entry(self, ctx, node)?;

        Ok((key, value))
    }

    type ListLiteralRet = TermId;

    fn visit_list_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListLiteral>,
    ) -> Result<Self::ListLiteralRet, Self::Error> {
        let walk::ListLiteral { elements } = walk::walk_list_literal(self, ctx, node)?;

        let list_inner_ty = self.core_defs().list_ty_fn;
        let element_ty = self.unify_term_sequence(elements)?;

        let builder = self.builder();
        let list_ty = builder.create_app_ty_fn_term(
            list_inner_ty,
            builder.create_args([builder.create_arg("T", element_ty)], ParamOrigin::TyFn),
        );

        let term = builder.create_rt_term(list_ty);

        // add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type SetLiteralRet = TermId;

    fn visit_set_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::SetLiteral>,
    ) -> Result<Self::SetLiteralRet, Self::Error> {
        let walk::SetLiteral { elements } = walk::walk_set_literal(self, ctx, node)?;

        let set_inner_ty = self.core_defs().set_ty_fn;
        let element_ty = self.unify_term_sequence(elements)?;

        let builder = self.builder();
        let set_ty = builder.create_app_ty_fn_term(
            set_inner_ty,
            builder.create_args([builder.create_arg("T", element_ty)], ParamOrigin::TyFn),
        );

        let term = builder.create_rt_term(set_ty);

        // add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type TupleLiteralEntryRet = Param;

    fn visit_tuple_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLiteralEntry>,
    ) -> Result<Self::TupleLiteralEntryRet, Self::Error> {
        let walk::TupleLiteralEntry { name, value, ty } =
            walk::walk_tuple_literal_entry(self, ctx, node)?;

        let ty_or_unresolved = ty.unwrap_or_else(|| self.builder().create_unresolved_term());
        let value_ty = self.typer().ty_of_term(value)?;

        // Append location to value term
        let value_location = self.source_location(node.value.span());
        self.location_store_mut().add_location_to_target(value_ty, value_location);

        // Check that the type of the value and the type annotation match and then apply
        // the substitution onto ty
        let ty_sub = self.unifier().unify_terms(value_ty, ty_or_unresolved)?;
        let ty = self.substituter().apply_sub_to_term(&ty_sub, ty_or_unresolved);

        let value = self.substituter().apply_sub_to_term(&ty_sub, value);

        Ok(Param { name, ty, default_value: Some(value) })
    }

    type TupleLiteralRet = TermId;

    fn visit_tuple_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::TupleLiteral>,
    ) -> Result<Self::TupleLiteralRet, Self::Error> {
        let walk::TupleLiteral { elements } = walk::walk_tuple_literal(self, ctx, node)?;
        let builder = self.builder();

        let params = builder.create_params(elements, ParamOrigin::Tuple);
        let term = builder.create_rt_term(builder.create_tuple_ty_term(params));

        // add the location of each parameter
        for (index, param) in node.elements.iter().enumerate() {
            let location = self.source_location(param.span());
            self.location_store_mut().add_location_to_target((params, index), location);
        }

        // add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type StrLiteralRet = TermId;

    fn visit_str_literal(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error> {
        let str_def = self.core_defs().str_ty;
        let ty = self.builder().create_nominal_def_term(str_def);
        let term = self.builder().create_rt_term(ty);

        // add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type CharLiteralRet = TermId;

    fn visit_char_literal(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error> {
        let char_def = self.core_defs().char_ty;
        let ty = self.builder().create_nominal_def_term(char_def);
        let term = self.builder().create_rt_term(ty);

        // add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type FloatLiteralRet = TermId;

    fn visit_float_literal(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error> {
        let f32_def = self.core_defs().f32_ty;
        let ty = self.builder().create_nominal_def_term(f32_def);
        let term = self.builder().create_rt_term(ty);

        // add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type BoolLiteralRet = TermId;

    fn visit_bool_literal(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BoolLiteral>,
    ) -> Result<Self::BoolLiteralRet, Self::Error> {
        let bool_def = self.core_defs().bool_ty;
        let ty = self.builder().create_nominal_def_term(bool_def);
        let term = self.builder().create_rt_term(ty);

        // add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type IntLiteralRet = TermId;

    fn visit_int_literal(
        &mut self,
        _: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error> {
        let i32_def = self.core_defs().i32_ty;
        let ty = self.builder().create_nominal_def_term(i32_def);
        let term = self.builder().create_rt_term(ty);

        // add the location of the term to the location storage
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type FunctionDefRet = TermId;

    fn visit_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FunctionDef>,
    ) -> Result<Self::FunctionDefRet, Self::Error> {
        let args: Vec<_> = node
            .params
            .iter()
            .map(|a| self.visit_function_def_param(ctx, a.ast_ref()))
            .collect::<TcResult<_>>()?;
        let return_ty =
            node.return_ty.as_ref().map(|t| self.visit_type(ctx, t.ast_ref())).transpose()?;

        let params_potentially_unresolved = self.builder().create_params(args, ParamOrigin::Fn);
        let param_scope = self.scope_resolver().enter_rt_param_scope(params_potentially_unresolved);

        let fn_body = self.visit_expression(ctx, node.fn_body.ast_ref())?;

        // @@Todo: deal with `return` statements inside the body
        let return_ty_or_unresolved = self.builder().or_unresolved_term(return_ty);
        let ty_of_body = self.typer().ty_of_term(fn_body)?;
        let body_sub = self.unifier().unify_terms(ty_of_body, return_ty_or_unresolved)?;

        let return_value = self.substituter().apply_sub_to_term(&body_sub, fn_body);
        let return_ty = self.substituter().apply_sub_to_term(&body_sub, return_ty_or_unresolved);
        let params =
            self.substituter().apply_sub_to_params(&body_sub, params_potentially_unresolved);

        // Add all the locations to the parameters
        // @@Todo(feds01): re-factor this into a helper function
        for (index, param) in node.params.iter().enumerate() {
            let location = self.source_location(param.span());
            self.location_store_mut().add_location_to_target((params, index), location);
        }

        // Remove the scope of the params after the body has been checked.
        self.scopes_mut().pop_the_scope(param_scope);

        let builder = self.builder();

        let fn_ty_term =
            builder.create_fn_lit_term(builder.create_fn_ty_term(params, return_ty), return_value);

        Ok(self.validator().validate_term(fn_ty_term)?.simplified_term_id)
    }

    type FunctionDefParamRet = Param;
    fn visit_function_def_param(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::FunctionDefParam>,
    ) -> Result<Self::FunctionDefParamRet, Self::Error> {
        let walk::FunctionDefParam { name, default, ty } =
            walk::walk_function_def_param(self, ctx, node)?;

        let ty_or_unresolved = self.builder().or_unresolved_term(ty);
        let value_or_unresolved = self.builder().or_unresolved_term(default);

        let value_ty = self.typer().ty_of_term(value_or_unresolved)?;
        let ty_sub = self.unifier().unify_terms(value_ty, ty_or_unresolved)?;

        let ty = self.substituter().apply_sub_to_term(&ty_sub, ty_or_unresolved);
        let value = self.substituter().apply_sub_to_term(&ty_sub, value_or_unresolved);

        Ok(Param { name: Some(name), ty, default_value: Some(value) })
    }

    type BlockRet = TermId;

    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        walk::walk_block_same_children(self, ctx, node)
    }

    type MatchCaseRet = TermId;

    fn visit_match_case(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        todo!()
    }

    type MatchBlockRet = TermId;

    fn visit_match_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        todo!()
    }

    type LoopBlockRet = TermId;

    fn visit_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let walk::LoopBlock(_) = walk::walk_loop_block(self, ctx, node)?;

        let void_ty = self.builder().create_void_ty_term();
        let term = self.builder().create_rt_term(void_ty);

        // Add the location of the type as the whole block
        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type ForLoopBlockRet = TermId;

    fn visit_for_loop_block(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        panic_on_span!(
            self.source_location(node.span()),
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
            self.source_location(node.span()),
            self.source_map(),
            "hit non de-sugared while-block whilst performing typechecking"
        );
    }

    type IfClauseRet = TermId;

    fn visit_if_clause(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        panic_on_span!(
            self.source_location(node.span()),
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
            self.source_location(node.span()),
            self.source_map(),
            "hit non de-sugared if-block whilst performing typechecking"
        );
    }

    type ModBlockRet = TermId;

    fn visit_mod_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        todo!()
    }

    type ImplBlockRet = TermId;

    fn visit_impl_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ImplBlock>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        todo!()
    }

    type BodyBlockRet = TermId;

    fn visit_body_block(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        // Traverse each statement
        for statement in node.statements.iter() {
            let statement_id = self.visit_expression(ctx, statement.ast_ref())?;
            self.validator().validate_term(statement_id)?;
            // @@Design: do we check that the return type is void? Should we
            // warn if it isn't?
        }

        // Traverse the ending expression, if any, or return void.
        match &node.expr {
            Some(expr) => {
                let expr_id = self.visit_expression(ctx, expr.ast_ref())?;

                Ok(self.validator().validate_term(expr_id)?.simplified_term_id)
            }
            None => {
                let builder = self.builder();
                Ok(builder.create_rt_term(builder.create_void_ty_term()))
            }
        }
    }

    type ReturnStatementRet = TermId;

    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        let walk::ReturnStatement(_) = walk::walk_return_statement(self, ctx, node)?;
        let builder = self.builder();

        let ret_ty = builder.create_void_ty_term();
        let term = builder.create_rt_term(ret_ty);

        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type BreakStatementRet = TermId;

    fn visit_break_statement(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        let builder = self.builder();
        let void_ty = builder.create_void_ty_term();
        let term = builder.create_rt_term(void_ty);

        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
    }

    type ContinueStatementRet = TermId;

    fn visit_continue_statement(
        &mut self,
        _ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        let builder = self.builder();
        let void_ty = builder.create_void_ty_term();
        let term = builder.create_rt_term(void_ty);

        let location = self.source_location(node.span());
        self.location_store_mut().add_location_to_target(term, location);

        Ok(term)
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
        // @@Todo: deal with mutability and visibility
        let walk::Declaration { pattern, ty, value } = walk::walk_declaration(self, ctx, node)?;

        // @@Todo: deal with other kinds of patterns:
        let name = match pattern {
            PatternHint::Binding { name } => name,
        };

        let ty_or_unresolved = self.builder().or_unresolved_term(ty);

        // Unify the type of the declaration with the type of the value of the
        // declaration.
        let sub = if let Some(value) = value {
            let ty_of_value = self.typer().ty_of_term(value)?;
            self.unifier().unify_terms(ty_of_value, ty_or_unresolved)?
        } else {
            Sub::empty()
        };

        // Apply the substitution on the type and value
        let value = value.map(|value| self.substituter().apply_sub_to_term(&sub, value));
        let ty = self.substituter().apply_sub_to_term(&sub, ty_or_unresolved);

        // Add the member to scope:
        let current_scope_id = self.scopes().current_scope();
        self.scope_store_mut().get_mut(current_scope_id).add(Member {
            name,
            data: MemberData::from_ty_and_value(Some(ty), value),
            mutability: Mutability::Immutable,
            visibility: Visibility::Private,
        });

        // Declaration should return its value if any:
        match value {
            Some(value) => Ok(value),
            // Void if no value:
            None => Ok(self.builder().create_void_ty_term()),
        }
    }

    type MergeDeclarationRet = TermId;

    fn visit_merge_declaration(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        todo!()
    }

    type AssignExpressionRet = TermId;

    fn visit_assign_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignExpression>,
    ) -> Result<Self::AssignExpressionRet, Self::Error> {
        todo!()
    }

    type AssignOpExpressionRet = TermId;

    fn visit_assign_op_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::AssignOpExpression>,
    ) -> Result<Self::AssignOpExpressionRet, Self::Error> {
        todo!()
    }

    type BinaryExpressionRet = TermId;

    fn visit_binary_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BinaryExpression>,
    ) -> Result<Self::BinaryExpressionRet, Self::Error> {
        todo!()
    }

    type UnaryExpressionRet = TermId;

    fn visit_unary_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::UnaryExpression>,
    ) -> Result<Self::UnaryExpressionRet, Self::Error> {
        todo!()
    }

    type IndexExpressionRet = TermId;

    fn visit_index_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IndexExpression>,
    ) -> Result<Self::IndexExpressionRet, Self::Error> {
        todo!()
    }

    type StructDefEntryRet = TermId;

    fn visit_struct_def_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::StructDefEntry>,
    ) -> Result<Self::StructDefEntryRet, Self::Error> {
        todo!()
    }

    type StructDefRet = TermId;

    fn visit_struct_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        todo!()
    }

    type EnumDefEntryRet = TermId;

    fn visit_enum_def_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        todo!()
    }

    type EnumDefRet = TermId;

    fn visit_enum_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        todo!()
    }

    type TraitDefRet = TermId;

    fn visit_trait_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        todo!()
    }

    type TraitImplRet = TermId;

    fn visit_trait_impl(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        todo!()
    }

    type PatternRet = PatternHint;

    fn visit_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::Pattern>,
    ) -> Result<Self::PatternRet, Self::Error> {
        walk::walk_pattern_same_children(self, ctx, node)
    }

    type ConstructorPatternRet = PatternHint;

    fn visit_constructor_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ConstructorPattern>,
    ) -> Result<Self::ConstructorPatternRet, Self::Error> {
        todo!()
    }

    type NamespacePatternRet = PatternHint;

    fn visit_namespace_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::NamespacePattern>,
    ) -> Result<Self::NamespacePatternRet, Self::Error> {
        todo!()
    }

    type TuplePatternEntryRet = TermId;

    fn visit_tuple_pattern_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePatternEntry>,
    ) -> Result<Self::TuplePatternEntryRet, Self::Error> {
        todo!()
    }

    type TuplePatternRet = PatternHint;

    fn visit_tuple_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::TuplePattern>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        todo!()
    }

    type ListPatternRet = PatternHint;

    fn visit_list_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::ListPattern>,
    ) -> Result<Self::ListPatternRet, Self::Error> {
        todo!()
    }

    type StrLiteralPatternRet = PatternHint;

    fn visit_str_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error> {
        todo!()
    }

    type CharLiteralPatternRet = PatternHint;

    fn visit_char_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error> {
        todo!()
    }

    type IntLiteralPatternRet = PatternHint;

    fn visit_int_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error> {
        todo!()
    }

    type FloatLiteralPatternRet = PatternHint;

    fn visit_float_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error> {
        todo!()
    }

    type BoolLiteralPatternRet = PatternHint;

    fn visit_bool_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::BoolLiteralPattern>,
    ) -> Result<Self::BoolLiteralPatternRet, Self::Error> {
        todo!()
    }

    type LiteralPatternRet = PatternHint;

    fn visit_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error> {
        todo!()
    }

    type OrPatternRet = PatternHint;

    fn visit_or_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::OrPattern>,
    ) -> Result<Self::OrPatternRet, Self::Error> {
        todo!()
    }

    type IfPatternRet = PatternHint;

    fn visit_if_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IfPattern>,
    ) -> Result<Self::IfPatternRet, Self::Error> {
        todo!()
    }

    type BindingPatternRet = PatternHint;

    fn visit_binding_pattern(
        &mut self,
        _: &Self::Ctx,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::BindingPattern>,
    ) -> Result<Self::BindingPatternRet, Self::Error> {
        Ok(PatternHint::Binding { name: node.name.body().ident })
    }

    type SpreadPatternRet = PatternHint;

    fn visit_spread_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::SpreadPattern>,
    ) -> Result<Self::SpreadPatternRet, Self::Error> {
        todo!()
    }

    type IgnorePatternRet = PatternHint;

    fn visit_ignore_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error> {
        todo!()
    }

    type DestructuringPatternRet = PatternHint;

    fn visit_destructuring_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::DestructuringPattern>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error> {
        todo!()
    }

    type ModuleRet = TermId;

    fn visit_module(
        &mut self,
        _ctx: &Self::Ctx,
        _node: hash_ast::ast::AstNodeRef<hash_ast::ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        todo!()
    }
}
