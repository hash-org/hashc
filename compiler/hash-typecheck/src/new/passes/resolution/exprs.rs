//! Resolution for expressions.
//!
//! This uses the [super::paths] module to convert AST expression nodes that
//! correspond to paths into terms. It does not handle general expressions,
//! which is handled later.

use hash_ast::ast::{self, AstNode, AstNodeId, AstNodeRef};
use hash_reporting::macros::panic_on_span;
use hash_source::location::Span;
use hash_types::{
    new::{
        access::AccessTerm,
        args::{ArgData, ArgsId},
        casting::CastTerm,
        control::{LoopControlTerm, LoopTerm, MatchTerm, ReturnTerm},
        data::DataTy,
        environment::{context::ScopeKind, env::AccessToEnv},
        fns::{FnBody, FnCallTerm},
        lits::{CharLit, FloatLit, IntLit, Lit, PrimTerm, StrLit},
        params::ParamIndex,
        refs::{DerefTerm, RefKind, RefTerm},
        scopes::{AssignTerm, BlockTerm, DeclStackMemberTerm},
        terms::{Term, TermId, UnsafeTerm},
        tuples::TupleTerm,
        tys::Ty,
    },
    term_as_variant,
};
use hash_utils::store::Store;
use itertools::{multiunzip, Itertools};

use super::{
    params::AstArgGroup,
    paths::{
        AstPath, AstPathComponent, NonTerminalResolvedPathComponent, ResolvedAstPathComponent,
        TerminalResolvedPathComponent,
    },
    scoping::ContextKind,
    ResolutionPass,
};
use crate::new::{
    diagnostics::error::{TcError, TcResult},
    environment::tc_env::AccessToTcEnv,
    ops::{common::CommonOps, AccessToOps},
    passes::ast_utils::AstUtils,
};

/// This block converts AST nodes of different kinds into [`AstPath`]s, in order
/// to later resolve them into terms.
impl<'tc> ResolutionPass<'tc> {
    /// Make TC arguments from the given set of AST tuple arguments.
    pub(super) fn make_args_from_ast_tuple_lit_args(
        &self,
        args: &ast::AstNodes<ast::TupleLitEntry>,
    ) -> TcResult<ArgsId> {
        // @@Todo: create type for the tuple as some annotations
        // might be given.
        // @@Todo: error recovery
        let args = args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                Ok(ArgData {
                    target: arg
                        .name
                        .as_ref()
                        .map(|name| ParamIndex::Name(name.ident))
                        .unwrap_or_else(|| ParamIndex::Position(i)),
                    value: self.make_term_from_ast_expr(arg.value.ast_ref())?,
                })
            })
            .collect::<TcResult<Vec<_>>>()?;
        Ok(self.param_ops().create_args(args.into_iter()))
    }

    /// Make TC arguments from the given set of AST constructor call arguments
    pub(super) fn make_args_from_constructor_call_args(
        &self,
        args: &ast::AstNodes<ast::ConstructorCallArg>,
    ) -> TcResult<ArgsId> {
        // @@Todo: error recovery
        let args = args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                Ok(ArgData {
                    target: arg
                        .name
                        .as_ref()
                        .map(|name| ParamIndex::Name(name.ident))
                        .unwrap_or_else(|| ParamIndex::Position(i)),
                    value: self.make_term_from_ast_expr(arg.value.ast_ref())?,
                })
            })
            .collect::<TcResult<Vec<_>>>()?;
        Ok(self.param_ops().create_args(args.into_iter()))
    }

    /// Make a term from the given [`ast::Expr`] and assign it to the node in
    /// the AST info store.
    ///
    /// This handles all expressions, some of which might be holes to be
    /// resolved later.
    pub(super) fn make_term_from_ast_expr(&self, node: AstNodeRef<ast::Expr>) -> TcResult<TermId> {
        // Maybe it has already been made:
        if let Some(term_id) = self.ast_info().terms().get_data_by_node(node.id()) {
            return Ok(term_id);
        }

        let term_id = match node.body {
            ast::Expr::Variable(variable_expr) => {
                self.make_term_from_ast_variable_expr(node.with_body(variable_expr))?
            }
            ast::Expr::ConstructorCall(ctor_expr) => {
                self.make_term_from_ast_constructor_call_expr(node.with_body(ctor_expr))?
            }
            ast::Expr::Access(access_expr) => {
                self.make_term_from_ast_access_expr(node.with_body(access_expr))?
            }
            ast::Expr::Ty(expr_ty) => self.make_term_from_ast_ty_expr(node.with_body(expr_ty))?,
            ast::Expr::Directive(directive_expr) => {
                self.make_term_from_ast_directive_expr(node.with_body(directive_expr))?
            }
            ast::Expr::Declaration(declaration) => {
                self.make_term_from_ast_stack_declaration(node.with_body(declaration))?
            }
            ast::Expr::Ref(ref_expr) => {
                self.make_term_from_ast_ref_expr(node.with_body(ref_expr))?
            }
            ast::Expr::Deref(deref_expr) => {
                self.make_term_from_ast_deref_expr(node.with_body(deref_expr))?
            }
            ast::Expr::Unsafe(unsafe_expr) => {
                self.make_term_from_ast_unsafe_expr(node.with_body(unsafe_expr))?
            }
            ast::Expr::Lit(lit_term) => {
                self.make_term_from_ast_lit_expr(node.with_body(lit_term))?
            }
            ast::Expr::Cast(cast_expr) => {
                self.make_term_from_ast_cast_expr(node.with_body(cast_expr))?
            }
            ast::Expr::Return(return_statement) => {
                self.make_term_from_ast_return_statement(node.with_body(return_statement))?
            }
            ast::Expr::Break(break_statement) => {
                self.make_term_from_ast_break_statement(node.with_body(break_statement))?
            }
            ast::Expr::Continue(continue_statement) => {
                self.make_term_from_ast_continue_statement(node.with_body(continue_statement))?
            }
            ast::Expr::Assign(assign_statement) => {
                self.make_term_from_ast_assign_expr(node.with_body(assign_statement))?
            }
            ast::Expr::Block(block_expr) => {
                self.make_term_from_ast_block_expr(node.with_body(block_expr))?
            }
            ast::Expr::TyFnDef(ty_fn_def) => {
                self.make_term_from_ast_ty_fn_def(node.with_body(ty_fn_def))?
            }
            ast::Expr::FnDef(fn_def) => self.make_term_from_ast_fn_def(node.with_body(fn_def))?,
            ast::Expr::AssignOp(assign_op_expr) => {
                self.make_term_from_ast_assign_op_expr(node.with_body(assign_op_expr))?
            }
            ast::Expr::Index(index_expr) => {
                self.make_term_from_ast_index_expr(node.with_body(index_expr))?
            }
            ast::Expr::BinaryExpr(binary_expr) => {
                self.make_term_from_ast_binary_expr(node.with_body(binary_expr))?
            }
            ast::Expr::UnaryExpr(unary_expr) => {
                self.make_term_from_ast_unary_expr(node.with_body(unary_expr))?
            }

            // No-ops (not supported or handled earlier):
            ast::Expr::Import(_)
            | ast::Expr::TraitDef(_)
            | ast::Expr::MergeDeclaration(_)
            | ast::Expr::ImplDef(_)
            | ast::Expr::TraitImpl(_) => self.new_void_term(),

            ast::Expr::StructDef(_) => {
                self.resolve_data_def_inner_terms(node)?;
                self.new_void_term()
            }
            ast::Expr::EnumDef(_) => {
                self.resolve_data_def_inner_terms(node)?;
                self.new_void_term()
            }
            ast::Expr::ModDef(mod_def) => {
                self.resolve_ast_mod_def_inner_terms(node.with_body(mod_def))?;
                self.new_void_term()
            }
        };

        self.ast_info().terms().insert(node.id(), term_id);
        Ok(term_id)
    }

    /// Use the given [`ast::VariableExpr`] as a path.
    fn variable_expr_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::VariableExpr>,
    ) -> TcResult<AstPath<'a>> {
        Ok(vec![AstPathComponent {
            name: node.body.name.ident,
            name_span: node.span(),
            args: vec![],
            node_id: node.id(),
        }])
    }

    /// Use the given [`ast::AccessExpr`] as a path, if applicable.
    ///
    /// Otherwise, this might be a struct/tuple property access, which is not a
    /// path, and this will return `None`.
    pub(super) fn access_expr_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::AccessExpr>,
    ) -> TcResult<Option<AstPath<'a>>> {
        match node.kind {
            ast::AccessKind::Namespace => match node.property.body() {
                ast::PropertyKind::NamedField(name) => {
                    let mut root =
                        self.expr_as_ast_path(node.body.subject.ast_ref())?.ok_or_else(|| {
                            TcError::InvalidNamespaceSubject { location: self.node_location(node) }
                        })?;
                    root.push(AstPathComponent {
                        name: *name,
                        name_span: node.property.span(),
                        args: vec![],
                        node_id: node.id(),
                    });
                    Ok(Some(root))
                }
                ast::PropertyKind::NumericField(_) => {
                    // Should have been caught at semantics
                    panic_on_span!(
                        self.node_location(node),
                        self.source_map(),
                        "Namespace followed by numeric field found"
                    )
                }
            },
            ast::AccessKind::Property => Ok(None),
        }
    }

    /// Use the given [`ast::ConstructorCallExpr`] as a path.
    fn constructor_call_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::ConstructorCallExpr>,
    ) -> TcResult<Option<AstPath<'a>>> {
        match self.expr_as_ast_path(node.body.subject.ast_ref())? {
            Some(mut path) => match path.last_mut() {
                Some(component) => {
                    component.args.push(AstArgGroup::ExplicitArgs(&node.body.args));
                    Ok(Some(path))
                }
                None => panic!("Expected at least one path component"),
            },
            None => Ok(None),
        }
    }

    /// Use the given [`ast::Expr`] as a path, if possible.
    ///
    /// Returns `None` if the expression is not a path. This is meant to
    /// be called from other `with_*_as_ast_path` functions.
    pub(super) fn expr_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::Expr>,
    ) -> TcResult<Option<AstPath<'a>>> {
        match node.body {
            ast::Expr::Variable(variable_expr) => {
                let variable_ref = node.with_body(variable_expr);
                Ok(Some(self.variable_expr_as_ast_path(variable_ref)?))
            }
            ast::Expr::ConstructorCall(ctor_expr) => {
                let ctor_ref = node.with_body(ctor_expr);
                self.constructor_call_as_ast_path(ctor_ref)
            }
            ast::Expr::Access(access_expr) => {
                let access_ref = node.with_body(access_expr);
                self.access_expr_as_ast_path(access_ref)
            }
            ast::Expr::Ty(expr_ty) => {
                let expr_ty_ref = node.with_body(expr_ty.ty.body());
                self.ty_as_ast_path(expr_ty_ref)
            }
            _ => Ok(None),
        }
    }

    /// Make a term from the given [`ResolvedAstPathComponent`].
    pub(super) fn make_term_from_resolved_ast_path(
        &self,
        path: &ResolvedAstPathComponent,
        original_node_span: Span,
    ) -> TcResult<TermId> {
        match path {
            ResolvedAstPathComponent::NonTerminal(non_terminal) => {
                match non_terminal {
                    NonTerminalResolvedPathComponent::Data(data_def_id, data_def_args) => {
                        // Data type
                        Ok(self.new_term(Term::Ty(self.new_ty(Ty::Data(DataTy {
                            data_def: *data_def_id,
                            args: *data_def_args,
                        })))))
                    }
                    NonTerminalResolvedPathComponent::Mod(_) => {
                        // Modules are not allowed in value positions
                        Err(TcError::CannotUseModuleInValuePosition {
                            location: self.source_location(original_node_span),
                        })
                    }
                }
            }
            ResolvedAstPathComponent::Terminal(terminal) => match terminal {
                TerminalResolvedPathComponent::FnDef(fn_def_id) => {
                    // Reference to a function definition
                    Ok(self.new_term(Term::FnRef(*fn_def_id)))
                }
                TerminalResolvedPathComponent::CtorPat(_) => {
                    panic_on_span!(
                        self.source_location(original_node_span),
                        self.source_map(),
                        "found CtorPat in value ast path"
                    )
                }
                TerminalResolvedPathComponent::CtorTerm(ctor_term) => {
                    // Constructor
                    Ok(self.new_term(Term::Ctor(*ctor_term)))
                }
                TerminalResolvedPathComponent::FnCall(fn_call_term) => {
                    // Function call
                    Ok(self.new_term(Term::FnCall(*fn_call_term)))
                }
                TerminalResolvedPathComponent::Var(bound_var) => {
                    // Bound variable
                    Ok(self.new_term(Term::Var(bound_var.name)))
                }
            },
        }
    }

    /// Make a term from an [`ast::VariableExpr`].
    fn make_term_from_ast_variable_expr(
        &self,
        node: AstNodeRef<ast::VariableExpr>,
    ) -> TcResult<TermId> {
        let path = self.variable_expr_as_ast_path(node)?;
        let resolved_path = self.resolve_ast_path(&path)?;
        self.make_term_from_resolved_ast_path(&resolved_path, node.span())
    }

    /// Make a term from an [`ast::ConstructorCallExpr`].
    fn make_term_from_ast_constructor_call_expr(
        &self,
        node: AstNodeRef<ast::ConstructorCallExpr>,
    ) -> TcResult<TermId> {
        // This is either a path or a computed function call
        match self.constructor_call_as_ast_path(node)? {
            Some(path) => {
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_term_from_resolved_ast_path(&resolved_path, node.span())
            }
            None => {
                let subject =
                    self.try_or_add_error(self.make_term_from_ast_expr(node.subject.ast_ref()));
                let args =
                    self.try_or_add_error(self.make_args_from_constructor_call_args(&node.args));

                match (subject, args) {
                    (Some(subject), Some(args)) => Ok(self.new_term(Term::FnCall(FnCallTerm {
                        subject,
                        args,
                        implicit: false,
                    }))),
                    _ => Err(TcError::Signal),
                }
            }
        }
    }

    /// Make a term from an [`ast::AccessExpr`].
    fn make_term_from_ast_access_expr(
        &self,
        node: AstNodeRef<ast::AccessExpr>,
    ) -> TcResult<TermId> {
        match self.access_expr_as_ast_path(node)? {
            Some(path) => {
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_term_from_resolved_ast_path(&resolved_path, node.span())
            }
            None => {
                // Namespace handled above.
                assert!(matches!(node.kind, ast::AccessKind::Property));

                let subject = self.make_term_from_ast_expr(node.subject.ast_ref())?;
                let field = match node.property.body() {
                    ast::PropertyKind::NamedField(name) => ParamIndex::Name(*name),
                    ast::PropertyKind::NumericField(number) => ParamIndex::Position(*number),
                };

                Ok(self.new_term(Term::Access(AccessTerm { subject, field })))
            }
        }
    }

    /// Make a term from an [`ast::TyExpr`].
    fn make_term_from_ast_ty_expr(&self, node: AstNodeRef<ast::TyExpr>) -> TcResult<TermId> {
        Ok(self.new_term(Term::Ty(self.make_ty_from_ast_ty(node.ty.ast_ref())?)))
    }

    /// Make a term from an [`ast::DirectiveExpr`].
    fn make_term_from_ast_directive_expr(
        &self,
        node: AstNodeRef<ast::DirectiveExpr>,
    ) -> TcResult<TermId> {
        // Pass to the inner expression
        // @@Future: keep directive in term structure
        self.make_term_from_ast_expr(node.subject.ast_ref())
    }

    /// Make a term from an [`ast::Declaration`] in non-constant scope.
    fn make_term_from_ast_stack_declaration(
        &self,
        node: AstNodeRef<ast::Declaration>,
    ) -> TcResult<TermId> {
        self.scoping().register_declaration(node);

        // Pattern
        let pat = self.try_or_add_error(self.make_pat_from_ast_pat(node.pat.ast_ref()));

        // Inner expression:
        let value = node
            .value
            .as_ref()
            .map(|v| self.try_or_add_error(self.make_term_from_ast_expr(v.ast_ref())));

        // Type annotation:
        let ty = node
            .ty
            .as_ref()
            .map(|ty| self.try_or_add_error(self.make_ty_from_ast_ty(ty.ast_ref())))
            .unwrap_or_else(|| Some(self.new_ty_hole()));

        match (pat, ty, value) {
            (Some(pat), Some(ty), Some(value)) => Ok(self
                .new_term(Term::DeclStackMember(DeclStackMemberTerm { bind_pat: pat, ty, value }))),
            _ => {
                // If pat had an error, then we can't make a term, and the
                // error will have been added already.
                Err(TcError::Signal)
            }
        }
    }

    /// Make a term from an [`ast::RefExpr`].
    fn make_term_from_ast_ref_expr(&self, node: AstNodeRef<ast::RefExpr>) -> TcResult<TermId> {
        let subject = self.make_term_from_ast_expr(node.inner_expr.ast_ref())?;
        Ok(self.new_term(Term::Ref(RefTerm {
            kind: match node.kind {
                ast::RefKind::Raw => RefKind::Raw,
                ast::RefKind::Normal => RefKind::Local,
            },
            mutable: node
                .mutability
                .as_ref()
                .map(|m| *m.body())
                .contains(&ast::Mutability::Mutable),
            subject,
        })))
    }

    /// Make a term from an [`ast::DerefExpr`].
    fn make_term_from_ast_deref_expr(&self, node: AstNodeRef<ast::DerefExpr>) -> TcResult<TermId> {
        let subject = self.make_term_from_ast_expr(node.data.ast_ref())?;
        Ok(self.new_term(Term::Deref(DerefTerm { subject })))
    }

    /// Make a term from an [`ast::UnsafeExpr`].
    fn make_term_from_ast_unsafe_expr(
        &self,
        node: AstNodeRef<ast::UnsafeExpr>,
    ) -> TcResult<TermId> {
        let inner = self.make_term_from_ast_expr(node.data.ast_ref())?;
        Ok(self.new_term(Term::Unsafe(UnsafeTerm { inner })))
    }

    /// Make a term from an [`ast::LitExpr`].
    fn make_term_from_ast_lit_expr(&self, node: AstNodeRef<ast::LitExpr>) -> TcResult<TermId> {
        // Macro to make a literal primitive term
        macro_rules! lit_prim {
            ($name:ident,$lit_name:ident, $contents:expr) => {
                self.new_term(Term::Prim(PrimTerm::Lit(Lit::$name($lit_name {
                    underlying: $contents,
                }))))
            };
        }

        match node.data.body() {
            ast::Lit::Str(str_lit) => Ok(lit_prim!(Str, StrLit, *str_lit)),
            ast::Lit::Char(char_lit) => Ok(lit_prim!(Char, CharLit, *char_lit)),
            ast::Lit::Int(int_lit) => Ok(lit_prim!(Int, IntLit, *int_lit)),
            ast::Lit::Float(float_lit) => Ok(lit_prim!(Float, FloatLit, *float_lit)),
            ast::Lit::Bool(bool_lit) => Ok(self.new_bool_term(bool_lit.data)),
            ast::Lit::Tuple(tuple_lit) => {
                let args = self.make_args_from_ast_tuple_lit_args(&tuple_lit.elements)?;
                // @@Todo: original_ty
                Ok(self.new_term(Term::Tuple(TupleTerm { data: args, original_ty: None })))
            }
            ast::Lit::Set(_) | ast::Lit::Map(_) | ast::Lit::List(_) => {
                unimplemented!("List, set, and map literals are not yet implemented")
            }
        }
    }

    /// Make a term from an [`ast::CastExpr`].
    fn make_term_from_ast_cast_expr(&self, node: AstNodeRef<ast::CastExpr>) -> TcResult<TermId> {
        let subject = self.try_or_add_error(self.make_term_from_ast_expr(node.expr.ast_ref()));
        let ty = self.try_or_add_error(self.make_ty_from_ast_ty(node.ty.ast_ref()));
        match (subject, ty) {
            (Some(subject), Some(ty)) => {
                Ok(self.new_term(Term::Cast(CastTerm { subject_term: subject, target_ty: ty })))
            }
            _ => Err(TcError::Signal),
        }
    }

    /// Make a term from an [`ast::ReturnStatement`].
    fn make_term_from_ast_return_statement(
        &self,
        node: AstNodeRef<ast::ReturnStatement>,
    ) -> TcResult<TermId> {
        let expression = match node.expr.as_ref() {
            Some(expr) => self.make_term_from_ast_expr(expr.ast_ref())?,
            None => self.new_void_term(),
        };
        Ok(self.new_term(Term::Return(ReturnTerm { expression })))
    }

    /// Make a term from an [`ast::BreakStatement`].
    fn make_term_from_ast_break_statement(
        &self,
        _: AstNodeRef<ast::BreakStatement>,
    ) -> TcResult<TermId> {
        Ok(self.new_term(Term::LoopControl(LoopControlTerm::Break)))
    }

    /// Make a term from an [`ast::ContinueStatement`].
    fn make_term_from_ast_continue_statement(
        &self,
        _: AstNodeRef<ast::ContinueStatement>,
    ) -> TcResult<TermId> {
        Ok(self.new_term(Term::LoopControl(LoopControlTerm::Continue)))
    }

    /// Make a term from an [`ast::AssignExpr`].
    fn make_term_from_ast_assign_expr(
        &self,
        node: AstNodeRef<ast::AssignExpr>,
    ) -> TcResult<TermId> {
        let lhs = self.try_or_add_error(self.make_term_from_ast_expr(node.lhs.ast_ref()));
        let rhs = self.try_or_add_error(self.make_term_from_ast_expr(node.rhs.ast_ref()));
        match (lhs, rhs) {
            (Some(lhs), Some(rhs)) => {
                Ok(self.new_term(Term::Assign(AssignTerm { subject: lhs, value: rhs })))
            }
            _ => Err(TcError::Signal),
        }
    }

    /// Make a term from an [`ast::MatchBlock`].
    fn make_term_from_ast_match_block(
        &self,
        node: AstNodeRef<ast::MatchBlock>,
    ) -> TcResult<TermId> {
        // First convert the subject
        let subject = self.try_or_add_error(self.make_term_from_ast_expr(node.subject.ast_ref()));

        // Convert all the cases and their bodies
        let cases_and_decisions: (Vec<_>, Vec<_>) =
            multiunzip(node.cases.iter().filter_map(|case| {
                self.scoping().enter_match_case(case.ast_ref(), |_| {
                    let pattern =
                        self.try_or_add_error(self.make_pat_from_ast_pat(case.pat.ast_ref()));
                    let body =
                        self.try_or_add_error(self.make_term_from_ast_expr(case.expr.ast_ref()));
                    match (pattern, body) {
                        (Some(pattern), Some(body)) => Some((pattern, body)),
                        _ => None,
                    }
                })
            }));

        // Create a term if all ok
        match (subject, cases_and_decisions.0.len() == node.cases.len()) {
            (Some(subject), true) => {
                let cases = self.new_pat_list(cases_and_decisions.0);
                let decisions = self.new_term_list(cases_and_decisions.1);
                Ok(self.new_term(Term::Match(MatchTerm { subject, cases, decisions })))
            }
            _ => Err(TcError::Signal),
        }
    }

    /// Make a term from an [`ast::BodyBlock`].
    ///
    /// If this block is not from a stack scope, this will panic.
    pub(super) fn make_term_from_ast_body_block(
        &self,
        node: AstNodeRef<ast::BodyBlock>,
    ) -> TcResult<TermId> {
        self.scoping()
            .enter_body_block(node, |_| {
                // Traverse the statements and the end expression
                let statements = node
                    .statements
                    .iter()
                    .filter_map(|statement| {
                        if let ast::Expr::Declaration(declaration) = statement.body() {
                            self.scoping().register_declaration(node.with_body(declaration));
                        }
                        self.try_or_add_error(self.make_term_from_ast_expr(statement.ast_ref()))
                    })
                    .collect_vec();
                let expr = node.expr.as_ref().map(|expr| {
                    self.try_or_add_error(self.make_term_from_ast_expr(expr.ast_ref()))
                });

                // If all ok, create a block term
                match (expr, statements.len() == node.statements.len()) {
                    (Some(expr), true) => {
                        let statements = self.new_term_list(statements);
                        let return_value = expr.unwrap_or_else(|| self.new_void_term());
                        Ok(self.new_term(Term::Block(BlockTerm { statements, return_value })))
                    }
                    _ => Err(TcError::Signal),
                }
            })
            .unwrap_or_else(|| {
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "Found non-stack body block in make_term_from_ast_body_block"
                )
            })
    }

    /// Make a term from an [`ast::LoopBlock`].
    fn make_term_from_ast_loop_block(&self, node: AstNodeRef<ast::LoopBlock>) -> TcResult<TermId> {
        let inner = self.make_term_from_ast_body_block(match node.contents.body() {
            ast::Block::Body(body_block) => node.contents.with_body(body_block),
            _ => panic_on_span!(
                self.node_location(node),
                self.source_map(),
                "Found non-body block in loop contents"
            ),
        })?;

        let block = term_as_variant!(self, value self.get_term(inner), Block);
        Ok(self.new_term(Term::Loop(LoopTerm { block })))
    }

    /// Make a term from an [`ast::BlockExpr`].
    fn make_term_from_ast_block_expr(&self, node: AstNodeRef<ast::BlockExpr>) -> TcResult<TermId> {
        match node.data.body() {
            ast::Block::Match(match_block) => {
                self.make_term_from_ast_match_block(node.data.with_body(match_block))
            }
            ast::Block::Loop(loop_block) => {
                self.make_term_from_ast_loop_block(node.data.with_body(loop_block))
            }
            ast::Block::Body(body_block) => {
                self.make_term_from_ast_body_block(node.data.with_body(body_block))
            }

            // Others done during de-sugaring:
            ast::Block::For(_) | ast::Block::While(_) | ast::Block::If(_) => {
                panic_on_span!(
                    self.node_location(node),
                    self.source_map(),
                    "Found non-desugared block in make_term_from_ast_block_expr"
                )
            }
        }
    }

    /// Make a function term from an AST function definition, which is either a
    /// [`ast::TyFnDef`] or a [`ast::FnDef`].
    fn make_term_from_some_ast_fn_def(
        &self,
        params: &ast::AstNodes<ast::Param>,
        body: &AstNode<ast::Expr>,
        return_ty: &Option<AstNode<ast::Ty>>,
        node_id: AstNodeId,
    ) -> TcResult<TermId> {
        // Function should already be discovered
        let fn_def_id = self.ast_info().fn_defs().get_data_by_node(node_id).unwrap();

        // First resolve the parameters
        let params = self.try_or_add_error(self.resolve_params_from_ast_params(
            params,
            self.stores().fn_def().map_fast(fn_def_id, |fn_def| fn_def.ty.implicit),
        ));

        // Modify the existing fn def for the params:
        if let Some(params) = params {
            self.stores().fn_def().modify_fast(fn_def_id, |fn_def| {
                fn_def.ty.params = params;
            });
        }

        let (return_ty, return_value, fn_def_id) =
            self.scoping().enter_scope(ScopeKind::Fn(fn_def_id), ContextKind::Environment, || {
                // In the scope of the parameters, resolve the return type and value
                let return_ty = return_ty.as_ref().map(|return_ty| {
                    self.try_or_add_error(self.make_ty_from_ast_ty(return_ty.ast_ref()))
                });

                // Modify the existing fn def for the return type:
                if let Some(Some(return_ty)) = return_ty {
                    self.stores().fn_def().modify_fast(fn_def_id, |fn_def| {
                        // This is a double option: one for potential error, another for not
                        // specifying return type.
                        fn_def.ty.return_ty = return_ty;
                    });
                }

                let return_value =
                    self.try_or_add_error(self.make_term_from_ast_expr(body.ast_ref()));

                // Modify the existing fn def for the return value:
                self.stores().fn_def().modify_fast(fn_def_id, |fn_def| {
                    if let Some(return_value) = return_value {
                        fn_def.body = FnBody::Defined(return_value);
                    }
                });

                (return_ty, return_value, fn_def_id)
            });

        // If all ok, create a fn ref term
        match (params, return_ty, return_value) {
            (Some(_), None | Some(Some(_)), Some(_)) => Ok(self.new_term(Term::FnRef(fn_def_id))),
            _ => Err(TcError::Signal),
        }
    }

    /// Make a term from an [`ast::TyFnDef`].
    pub(super) fn make_term_from_ast_ty_fn_def(
        &self,
        node: AstNodeRef<ast::TyFnDef>,
    ) -> TcResult<TermId> {
        self.make_term_from_some_ast_fn_def(
            &node.params,
            &node.ty_fn_body,
            &node.return_ty,
            node.id(),
        )
    }

    /// Make a term from an [`ast::FnDef`].
    pub(super) fn make_term_from_ast_fn_def(
        &self,
        node: AstNodeRef<ast::FnDef>,
    ) -> TcResult<TermId> {
        self.make_term_from_some_ast_fn_def(&node.params, &node.fn_body, &node.return_ty, node.id())
    }

    /// Make a term from an [`ast::AssignOpExpr`].
    fn make_term_from_ast_assign_op_expr(
        &self,
        _node: AstNodeRef<ast::AssignOpExpr>,
    ) -> TcResult<TermId> {
        // @@Todo: deal with operators
        todo!()
    }

    /// Make a term from an [`ast::IndexExpr`].
    fn make_term_from_ast_index_expr(&self, _node: AstNodeRef<ast::IndexExpr>) -> TcResult<TermId> {
        // @@Todo: deal with indexing
        todo!()
    }

    /// Make a term from an [`ast::BinaryExpr`].
    fn make_term_from_ast_binary_expr(
        &self,
        _node: AstNodeRef<ast::BinaryExpr>,
    ) -> TcResult<TermId> {
        // @@Todo: deal with operators
        todo!()
    }

    /// Make a term from an [`ast::UnaryExpr`].
    fn make_term_from_ast_unary_expr(&self, _node: AstNodeRef<ast::UnaryExpr>) -> TcResult<TermId> {
        // @@Todo: deal with operators
        todo!()
    }
}
