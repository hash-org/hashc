//! Resolution for expressions.
//!
//! This uses the [super::paths] module to convert AST expression nodes that
//! correspond to paths into terms. It does not handle general expressions,
//! which is handled later.

use std::collections::HashSet;

use hash_ast::ast::{self, AstNode, AstNodeId, AstNodeRef};
use hash_ast_utils::lit::LitHelpers;
use hash_attrs::{attr::attr_store, builtin::attrs};
use hash_const_eval::op::{BinOp, LogicalBinOp, UnOp};
use hash_reporting::macros::panic_on_span;
use hash_storage::store::{
    SequenceStoreKey, TrivialSequenceStoreKey,
    statics::{SequenceStoreValue, StoreId},
};
use hash_tir::{
    intrinsics::{
        definitions::{Intrinsic, equal_ty},
        utils::{bool_term, create_term_from_const},
    },
    tir::{
        AccessTerm, AnnotTerm, Arg, ArgsId, ArrayTerm, CallTerm, DataTy, DerefTerm, IndexTerm, Lit,
        LoopControlTerm, LoopTerm, MatchCase, MatchTerm, Node, NodeId, NodeOrigin, ParamIndex,
        RefKind, RefTerm, ReturnTerm, Term, TermId, TupleTerm, Ty, TyOfTerm, UnsafeTerm, VarTerm,
        blocks::{BlockStatement, BlockTerm, Decl},
        commands::AssignTerm,
    },
};
use hash_utils::itertools::Itertools;

use super::{
    ResolutionPass,
    params::AstArgGroup,
    paths::{
        AstPath, AstPathComponent, NonTerminalResolvedPathComponent, ResolvedAstPathComponent,
        TerminalResolvedPathComponent,
    },
    scoping::ContextKind,
};
use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult},
    env::SemanticEnv,
    passes::analysis_pass::AnalysisPass,
};

pub enum AstParams<'ast> {
    Ty(&'ast ast::AstNode<ast::TyParams>),
    Param(&'ast ast::AstNode<ast::Params>),
}

/// This block converts AST nodes of different kinds into [`AstPath`]s, in order
/// to later resolve them into terms.
impl<E: SemanticEnv> ResolutionPass<'_, E> {
    /// Make TC arguments from the given set of AST tuple arguments.
    pub(super) fn make_args_from_ast_tuple_expr_args(
        &self,
        args: &ast::AstNodes<ast::ExprArg>,
    ) -> SemanticResult<ArgsId> {
        // @@Todo: create type for the tuple as some annotations
        // might be given.
        // @@Todo: error recovery
        let created_args = args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let value = self.apply_directives(arg.macros.as_ref(), arg.value.ast_ref())?;

                Ok(Node::at(
                    Arg {
                        target: arg
                            .name
                            .as_ref()
                            .map(|name| ParamIndex::Name(name.ident))
                            .unwrap_or_else(|| ParamIndex::pos(i)),
                        value,
                    },
                    NodeOrigin::Given(arg.id()),
                ))
            })
            .collect::<SemanticResult<Vec<_>>>()?;
        Ok(Node::create_at(Node::<Arg>::seq(created_args), NodeOrigin::Given(args.id())))
    }

    /// Make TC arguments from the given set of AST constructor call arguments
    pub(super) fn make_args_from_constructor_call_args(
        &self,
        args: &ast::AstNodes<ast::ExprArg>,
    ) -> SemanticResult<ArgsId> {
        // @@Todo: error recovery
        let created_args = args
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let value = self.apply_directives(arg.macros.as_ref(), arg.value.ast_ref())?;

                Ok(Node::at(
                    Arg {
                        target: arg
                            .name
                            .as_ref()
                            .map(|name| ParamIndex::Name(name.ident))
                            .unwrap_or_else(|| ParamIndex::pos(i)),
                        value,
                    },
                    NodeOrigin::Given(arg.id()),
                ))
            })
            .collect::<SemanticResult<Vec<_>>>()?;
        Ok(Node::create_at(Node::<Arg>::seq(created_args), NodeOrigin::Given(args.id())))
    }

    /// Make a term from the given [`ast::Expr`] and assign it to the node in
    /// the AST info store.
    ///
    /// This handles all expressions, some of which might be holes to be
    /// resolved later.
    pub(super) fn make_term_from_ast_expr(
        &self,
        node: AstNodeRef<ast::Expr>,
    ) -> SemanticResult<TermId> {
        let term_id = match node.body {
            ast::Expr::Variable(variable_expr) => {
                self.make_term_from_ast_variable_expr(node.with_body(variable_expr))?
            }
            ast::Expr::ImplicitCall(implicit_call) => {
                self.make_ty_from_ast_implicit_fn_call(node.with_body(implicit_call))?
            }
            ast::Expr::Call(ctor_expr) => {
                self.make_term_from_ast_call_expr(node.with_body(ctor_expr))?
            }
            ast::Expr::Access(access_expr) => {
                self.make_term_from_ast_access_expr(node.with_body(access_expr))?
            }
            ast::Expr::Ty(expr_ty) => self.make_ty_from_ast_ty(expr_ty.ty.ast_ref())?,
            ast::Expr::Macro(invocation) => {
                self.make_term_from_ast_macro_invocation_expr(node.with_body(invocation))?
            }
            ast::Expr::TokenMacro(_) => panic!("un-expanded token macro in resolution"),
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
            ast::Expr::Tuple(tuple_lit) => {
                let args = self.make_args_from_ast_tuple_expr_args(&tuple_lit.elements)?;
                Term::from(Term::Tuple(TupleTerm { data: args }), NodeOrigin::Given(node.id()))
            }
            ast::Expr::Array(array_lit) => {
                let element_vec: Vec<_> = array_lit
                    .elements
                    .ast_ref_iter()
                    .map(|element| self.make_term_from_ast_expr(element))
                    .collect::<SemanticResult<_>>()?;
                let elements =
                    Node::create_at(TermId::seq(element_vec), NodeOrigin::Given(node.id()));
                Term::from(Term::Array(ArrayTerm::Normal(elements)), NodeOrigin::Given(node.id()))
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
            ast::Expr::ImplicitFnDef(def) => {
                self.make_term_from_ast_implicit_fn_def(node.with_body(def))?
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

            ast::Expr::Import(import_expr) => {
                let source_id = import_expr.data.source;
                ResolutionPass::new(self.env, self.ast_info).pass_source(source_id)?;
                Term::unit(NodeOrigin::Given(node.id()))
            }

            // No-ops (handled earlier):
            ast::Expr::Declaration(_) => Term::unit(NodeOrigin::Given(node.id())),

            ast::Expr::StructDef(_) => {
                self.resolve_data_def_inner_terms(node)?;
                Term::unit(NodeOrigin::Given(node.id()))
            }
            ast::Expr::EnumDef(_) => {
                self.resolve_data_def_inner_terms(node)?;
                Term::unit(NodeOrigin::Given(node.id()))
            }
            ast::Expr::ModDef(mod_def) => {
                self.resolve_ast_mod_def_inner_terms(node.with_body(mod_def))?;
                Term::unit(NodeOrigin::Given(node.id()))
            }
            ast::Expr::Repeat(repeat_expr) => {
                self.make_term_from_repeat_expr(node.with_body(repeat_expr))?
            }
        };

        self.ast_info.terms().insert(node.id(), term_id);
        Ok(term_id)
    }

    /// Use the given [`ast::VariableExpr`] as a path.
    fn variable_expr_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::VariableExpr>,
    ) -> SemanticResult<AstPath<'a>> {
        Ok(vec![AstPathComponent {
            name: node.name.ident,
            name_node_id: node.name.id(),
            args: Node::at(vec![], NodeOrigin::Given(node.id())),
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
    ) -> SemanticResult<Option<AstPath<'a>>> {
        match node.kind {
            ast::AccessKind::Namespace => match node.property.body() {
                ast::PropertyKind::NamedField(name) => {
                    let mut root =
                        self.expr_as_ast_path(node.body.subject.ast_ref())?.ok_or_else(|| {
                            SemanticError::InvalidNamespaceSubject { location: node.span() }
                        })?;
                    root.push(AstPathComponent {
                        name: *name,
                        name_node_id: node.property.id(),
                        args: Node::at(vec![], NodeOrigin::Given(node.id())),
                        node_id: node.id(),
                    });
                    Ok(Some(root))
                }
                ast::PropertyKind::NumericField(_) => {
                    // Should have been caught at semantics
                    panic_on_span!(node.span(), "Namespace followed by numeric field found")
                }
            },
            ast::AccessKind::Property => Ok(None),
        }
    }

    /// Use the given [`ast::CallExpr`] as a path.
    fn call_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::CallExpr>,
    ) -> SemanticResult<Option<AstPath<'a>>> {
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
    ) -> SemanticResult<Option<AstPath<'a>>> {
        match node.body {
            ast::Expr::Variable(variable_expr) => {
                let variable_ref = node.with_body(variable_expr);
                Ok(Some(self.variable_expr_as_ast_path(variable_ref)?))
            }
            ast::Expr::Call(call_expr) => {
                let call_ref = node.with_body(call_expr);
                self.call_as_ast_path(call_ref)
            }
            ast::Expr::Access(access_expr) => {
                let access_ref = node.with_body(access_expr);
                self.access_expr_as_ast_path(access_ref)
            }
            ast::Expr::Ty(expr_ty) => {
                let expr_ty_ref = node.with_body(expr_ty.ty.body());
                self.ty_as_ast_path(expr_ty_ref)
            }
            ast::Expr::ImplicitCall(implicit_call) => {
                let call_ref = node.with_body(implicit_call);
                self.implicit_call_as_ast_path(call_ref)
            }
            _ => Ok(None),
        }
    }

    /// Make a term from the given [`ResolvedAstPathComponent`].
    pub(super) fn make_term_from_resolved_ast_path(
        &self,
        path: &ResolvedAstPathComponent,
        original_node_id: AstNodeId,
    ) -> SemanticResult<TermId> {
        let origin = NodeOrigin::Given(original_node_id);
        match path {
            ResolvedAstPathComponent::NonTerminal(non_terminal) => {
                match non_terminal {
                    NonTerminalResolvedPathComponent::Data(data_def_id, data_def_args) => {
                        // Data type
                        Ok(Term::from(
                            Ty::DataTy(DataTy { data_def: *data_def_id, args: *data_def_args }),
                            origin,
                        ))
                    }
                    NonTerminalResolvedPathComponent::Mod(_) => {
                        // Modules are not allowed in value positions
                        Err(SemanticError::CannotUseModuleInValuePosition {
                            location: original_node_id.span(),
                        })
                    }
                }
            }
            ResolvedAstPathComponent::Terminal(terminal) => match terminal {
                TerminalResolvedPathComponent::FnDef(fn_def_id) => {
                    // Reference to a function definition
                    Ok(Term::from(Term::Fn(*fn_def_id), origin))
                }
                TerminalResolvedPathComponent::CtorPat(_) => {
                    panic_on_span!(original_node_id.span(), "found CtorPat in value ast path")
                }
                TerminalResolvedPathComponent::CtorTerm(ctor_term) => {
                    // Constructor
                    Ok(Term::from(Term::Ctor(**ctor_term), origin))
                }
                TerminalResolvedPathComponent::FnCall(fn_call_term) => {
                    // Function call
                    Ok(Term::from(Term::Call(**fn_call_term), origin))
                }
                TerminalResolvedPathComponent::Var(bound_var) => {
                    // Bound variable
                    Ok(Term::from(Term::Var(VarTerm { symbol: *bound_var }), origin))
                }
                TerminalResolvedPathComponent::Intrinsic(intrinsic) => {
                    // Intrinsic
                    Ok(Term::from(Term::Intrinsic(*intrinsic), origin))
                }
            },
        }
    }

    /// Make a term from an [`ast::VariableExpr`].
    fn make_term_from_ast_variable_expr(
        &self,
        node: AstNodeRef<ast::VariableExpr>,
    ) -> SemanticResult<TermId> {
        let path = self.variable_expr_as_ast_path(node)?;
        let resolved_path = self.resolve_ast_path(&path)?;
        self.make_term_from_resolved_ast_path(&resolved_path, node.id())
    }

    /// Make a term from an [`ast::CallExpr`].
    fn make_term_from_ast_call_expr(
        &self,
        node: AstNodeRef<ast::CallExpr>,
    ) -> SemanticResult<TermId> {
        // This is either a path or a computed function call
        match self.call_as_ast_path(node)? {
            Some(path) => {
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_term_from_resolved_ast_path(&resolved_path, node.id())
            }
            None => {
                let subject =
                    self.try_or_add_error(self.make_term_from_ast_expr(node.subject.ast_ref()));
                let args =
                    self.try_or_add_error(self.make_args_from_constructor_call_args(&node.args));

                match (subject, args) {
                    (Some(subject), Some(args)) => Ok(Term::from(
                        Term::Call(CallTerm { subject, args, implicit: false }),
                        NodeOrigin::Given(node.id()),
                    )),
                    _ => Err(SemanticError::Signal),
                }
            }
        }
    }

    /// Make a term from an [`ast::AccessExpr`].
    fn make_term_from_ast_access_expr(
        &self,
        node: AstNodeRef<ast::AccessExpr>,
    ) -> SemanticResult<TermId> {
        match self.access_expr_as_ast_path(node)? {
            Some(path) => {
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_term_from_resolved_ast_path(&resolved_path, node.id())
            }
            None => {
                // Namespace handled above.
                assert!(matches!(node.kind, ast::AccessKind::Property));

                let subject = self.make_term_from_ast_expr(node.subject.ast_ref())?;
                let field = match node.property.body() {
                    ast::PropertyKind::NamedField(name) => ParamIndex::Name(*name),
                    ast::PropertyKind::NumericField(number) => ParamIndex::Position(*number),
                };

                Ok(Term::from(
                    Term::Access(AccessTerm { subject, field }),
                    NodeOrigin::Given(node.id()),
                ))
            }
        }
    }

    /// Make a term from an [`ast::ExprMacroInvocation`].
    fn make_term_from_ast_macro_invocation_expr(
        &self,
        node: AstNodeRef<ast::ExprMacroInvocation>,
    ) -> SemanticResult<TermId> {
        // Here, we need to check what kind of invocation this is, and whether we need
        // to map into an intrinsic call.
        let ast::ExprMacroInvocation { macros, subject } = node.body();
        self.apply_directives(Some(macros), subject.ast_ref())
    }

    /// Make a term from an [`ast::Declaration`] in non-constant scope.
    fn make_decl_from_ast_declaration(
        &self,
        node: AstNodeRef<ast::Declaration>,
    ) -> SemanticResult<Node<Decl>> {
        self.scoping().register_declaration(node);

        // Pattern
        let pat =
            self.try_or_add_error(self.make_pat_from_ast_pat_and_check_binds(node.pat.ast_ref()));

        // Initialiser:
        let value = self.try_or_add_error(self.make_term_from_ast_expr(node.value.ast_ref()));

        // Type annotation:
        let ty = match node.ty.as_ref() {
            Some(ty) => self.try_or_add_error(self.make_ty_from_ast_ty(ty.ast_ref())),
            None => Some(Ty::hole(NodeOrigin::InferredFrom(node.value.id()))),
        };

        match (pat, ty, value) {
            (Some(pat), Some(ty), Some(value)) => {
                Ok(Node::at(Decl { bind_pat: pat, ty, value }, NodeOrigin::Given(node.id())))
            }
            _ => {
                // If pat had an error, then we can't make a term, and the
                // error will have been added already.
                Err(SemanticError::Signal)
            }
        }
    }

    /// Make a term from an [`ast::RefExpr`].
    fn make_term_from_ast_ref_expr(
        &self,
        node: AstNodeRef<ast::RefExpr>,
    ) -> SemanticResult<TermId> {
        let subject = self.make_term_from_ast_expr(node.inner_expr.ast_ref())?;
        Ok(Term::from(
            Term::Ref(RefTerm {
                kind: match node.kind {
                    ast::RefKind::Raw => RefKind::Raw,
                    ast::RefKind::Normal => RefKind::Local,
                },
                mutable: node
                    .mutability
                    .as_ref()
                    .map(|m| *m.body())
                    .is_some_and(|mutability| mutability == ast::Mutability::Mutable),
                subject,
            }),
            NodeOrigin::Given(node.id()),
        ))
    }

    /// Make a term from an [`ast::DerefExpr`].
    fn make_term_from_ast_deref_expr(
        &self,
        node: AstNodeRef<ast::DerefExpr>,
    ) -> SemanticResult<TermId> {
        let subject = self.make_term_from_ast_expr(node.data.ast_ref())?;
        Ok(Term::from(Term::Deref(DerefTerm { subject }), NodeOrigin::Given(node.id())))
    }

    /// Make a term from an [`ast::UnsafeExpr`].
    fn make_term_from_ast_unsafe_expr(
        &self,
        node: AstNodeRef<ast::UnsafeExpr>,
    ) -> SemanticResult<TermId> {
        let inner = self.make_term_from_ast_expr(node.data.ast_ref())?;
        Ok(Term::from(Term::Unsafe(UnsafeTerm { inner }), NodeOrigin::Given(node.id())))
    }

    /// Make a term from an [`ast::Lit`].
    fn make_term_from_ast_lit(&self, node: AstNodeRef<ast::Lit>) -> SemanticResult<TermId> {
        // Macro to make a literal primitive term
        macro_rules! lit_prim {
            ($name:ident, $contents:expr) => {
                Term::from(
                    Term::Lit(Node::create_at(Lit::$name($contents), NodeOrigin::Given(node.id()))),
                    NodeOrigin::Given(node.id()),
                )
            };
        }

        match node.body() {
            // @@Future: perhaps this can just be a const too...
            ast::Lit::Bool(bool_lit) => Ok(bool_term(bool_lit.data, NodeOrigin::Given(node.id()))),
            ast::Lit::Int(int_lit) => Ok(lit_prim!(Int, *int_lit)),
            ast::Lit::Float(float_lit) => Ok(lit_prim!(Float, *float_lit)),
            // ##Note: Converting to a `Const` here is infallible since we don't handle floats/ints
            // until later when we actually bake them.
            lit => Ok(lit_prim!(Const, lit.to_const(None, self.target().ptr_size()).unwrap())),
        }
    }

    /// Make a term from an [`ast::LitExpr`].
    fn make_term_from_ast_lit_expr(
        &self,
        node: AstNodeRef<ast::LitExpr>,
    ) -> SemanticResult<TermId> {
        self.make_term_from_ast_lit(node.with_body(node.data.body()))
    }

    /// Make a term from an [`ast::CastExpr`].
    fn make_term_from_ast_cast_expr(
        &self,
        node: AstNodeRef<ast::CastExpr>,
    ) -> SemanticResult<TermId> {
        let subject = self.try_or_add_error(self.make_term_from_ast_expr(node.expr.ast_ref()));
        let ty = self.try_or_add_error(self.make_ty_from_ast_ty(node.ty.ast_ref()));
        match (subject, ty) {
            (Some(subject), Some(ty)) => Ok(Term::from(
                Term::Annot(AnnotTerm { subject_term: subject, target_ty: ty }),
                NodeOrigin::Given(node.id()),
            )),
            _ => Err(SemanticError::Signal),
        }
    }

    /// Make a term from an [`ast::ReturnStatement`].
    fn make_term_from_ast_return_statement(
        &self,
        node: AstNodeRef<ast::ReturnStatement>,
    ) -> SemanticResult<TermId> {
        let expression = match node.expr.as_ref() {
            Some(expr) => self.make_term_from_ast_expr(expr.ast_ref())?,
            None => Term::unit(NodeOrigin::Given(node.id())),
        };
        Ok(Term::from(Term::Return(ReturnTerm { expression }), NodeOrigin::Given(node.id())))
    }

    /// Make a term from an [`ast::BreakStatement`].
    fn make_term_from_ast_break_statement(
        &self,
        node: AstNodeRef<ast::BreakStatement>,
    ) -> SemanticResult<TermId> {
        Ok(Term::from(Term::LoopControl(LoopControlTerm::Break), NodeOrigin::Given(node.id())))
    }

    /// Make a term from an [`ast::ContinueStatement`].
    fn make_term_from_ast_continue_statement(
        &self,
        node: AstNodeRef<ast::ContinueStatement>,
    ) -> SemanticResult<TermId> {
        Ok(Term::from(Term::LoopControl(LoopControlTerm::Continue), NodeOrigin::Given(node.id())))
    }

    /// Make a term from an [`ast::AssignExpr`].
    fn make_term_from_ast_assign_expr(
        &self,
        node: AstNodeRef<ast::AssignExpr>,
    ) -> SemanticResult<TermId> {
        let lhs = self.try_or_add_error(self.make_term_from_ast_expr(node.lhs.ast_ref()));
        let rhs = self.try_or_add_error(self.make_term_from_ast_expr(node.rhs.ast_ref()));

        match (lhs, rhs) {
            (Some(lhs), Some(rhs)) => Ok(Term::from(
                Term::Assign(AssignTerm { subject: lhs, value: rhs }),
                NodeOrigin::Given(node.id()),
            )),
            _ => Err(SemanticError::Signal),
        }
    }

    /// Make a term from an [`ast::MatchBlock`].
    fn make_term_from_ast_match_block(
        &self,
        node: AstNodeRef<ast::MatchBlock>,
    ) -> SemanticResult<TermId> {
        // First convert the subject
        let subject = self.try_or_add_error(self.make_term_from_ast_expr(node.subject.ast_ref()));

        // Convert all the cases and their bodies
        let cases = Node::create_at(
            Node::<MatchCase>::seq(
                node.cases
                    .iter()
                    .filter_map(|case| {
                        self.scoping().enter_match_case(case.ast_ref(), |stack_id| {
                            let bind_pat = self.try_or_add_error(
                                self.make_pat_from_ast_pat_and_check_binds(case.pat.ast_ref()),
                            );
                            let value = self.try_or_add_error(
                                self.make_term_from_ast_expr(case.expr.ast_ref()),
                            );
                            match (bind_pat, value) {
                                (Some(bind_pat), Some(value)) => Some(Node::at(
                                    MatchCase { bind_pat, value, stack_id },
                                    NodeOrigin::Given(case.id()),
                                )),
                                _ => None,
                            }
                        })
                    })
                    .collect_vec(),
            ),
            NodeOrigin::Given(node.cases.id()),
        );

        // Create a term if all ok
        match (subject, cases.len() == node.cases.len()) {
            (Some(subject), true) => Ok(Term::from(
                Term::Match(MatchTerm { subject, cases, origin: node.origin }),
                NodeOrigin::Given(node.id()),
            )),
            _ => Err(SemanticError::Signal),
        }
    }

    /// Make a term from an [`ast::BodyBlock`].
    ///
    /// If this block is not from a stack scope, this will panic.
    pub(super) fn make_term_from_ast_body_block(
        &self,
        node: AstNodeRef<ast::BodyBlock>,
    ) -> SemanticResult<TermId> {
        self.scoping()
            .enter_body_block(node, |stack_id| {
                // Keep track of the ids of the mod members
                let mut mod_member_ids = HashSet::new();

                // First handle local mod members
                if let Some(local_mod_def) = stack_id.borrow().local_mod_def {
                    let local_mod_members = local_mod_def.borrow().members;

                    // Get the ids of the local mod members
                    mod_member_ids.extend(local_mod_members.iter().map(|member_id| {
                        self.ast_info.mod_members().get_node_by_data(member_id).unwrap()
                    }));

                    // Resolve them
                    self.resolve_mod_def_inner_terms(
                        local_mod_def,
                        node.statements
                            .ast_ref_iter()
                            .chain(node.expr.as_ref().map(|expr| expr.ast_ref()))
                            .filter(|statement| mod_member_ids.contains(&statement.id())),
                    )?;

                    // Enter the scope of the module
                    self.scoping().add_mod_members(local_mod_def);
                }

                // Traverse the statements:
                let mut statements = node
                    .statements
                    .iter()
                    .filter(|statement| !mod_member_ids.contains(&statement.id()))
                    .filter_map(|statement| {
                        if let ast::Expr::Declaration(declaration) = statement.body() {
                            // Handle declarations using `BlockStatement::Decl`
                            self.scoping().register_declaration(node.with_body(declaration));
                            let decl =
                                self.try_or_add_error(self.make_decl_from_ast_declaration(
                                    statement.with_body(declaration),
                                ))?;
                            Some(decl.with_data(BlockStatement::Decl(decl.data)))
                        } else {
                            // Everything else is `BlockStatement::Expr`
                            let expr = self.try_or_add_error(
                                self.make_term_from_ast_expr(statement.ast_ref()),
                            )?;
                            Some(Node::at(BlockStatement::Expr(expr), expr.origin()))
                        }
                    })
                    .collect_vec();

                // If an expression is given, use it as the returning expression, and otherwise
                // use a unit `()` as the returning expression.
                let total_origin = NodeOrigin::Given(node.id());
                let empty_expr = || Term::unit(total_origin);
                let expr = match node.expr.as_ref() {
                    Some(expr) => {
                        if mod_member_ids.contains(&expr.id()) {
                            Some(empty_expr())
                        } else if let ast::Expr::Declaration(declaration) = expr.body() {
                            self.try_or_add_error(
                                self.make_decl_from_ast_declaration(expr.with_body(declaration)),
                            )
                            .map(|decl| {
                                statements.push(decl.with_data(BlockStatement::Decl(decl.data)));
                                empty_expr()
                            })
                        } else {
                            self.try_or_add_error(self.make_term_from_ast_expr(expr.ast_ref()))
                        }
                    }
                    None => Some(empty_expr()),
                };

                // If all ok, create a block term
                match expr {
                    Some(expr) => {
                        let statements =
                            Node::create_at(Node::seq(statements), NodeOrigin::Given(node.id()));
                        let result = Term::from(
                            Term::Block(BlockTerm { statements, expr, stack_id }),
                            NodeOrigin::Given(node.id()),
                        );
                        Ok(result)
                    }
                    _ => Err(SemanticError::Signal),
                }
            })
            .unwrap_or_else(|| {
                panic_on_span!(
                    node.span(),
                    "Found non-stack body block in make_term_from_ast_body_block"
                )
            })
    }

    /// Make a term from an [`ast::LoopBlock`].
    fn make_term_from_ast_loop_block(
        &self,
        node: AstNodeRef<ast::LoopBlock>,
    ) -> SemanticResult<TermId> {
        let inner = self.make_term_from_ast_block(node.contents.ast_ref())?;
        Ok(Term::from(Term::Loop(LoopTerm { inner }), NodeOrigin::Given(node.id())))
    }

    /// Make a term from an [`ast::Block`].
    fn make_term_from_ast_block(&self, node: AstNodeRef<ast::Block>) -> SemanticResult<TermId> {
        match node.body() {
            ast::Block::Match(match_block) => {
                self.make_term_from_ast_match_block(node.with_body(match_block))
            }
            ast::Block::Loop(loop_block) => {
                self.make_term_from_ast_loop_block(node.with_body(loop_block))
            }
            ast::Block::Body(body_block) => {
                self.make_term_from_ast_body_block(node.with_body(body_block))
            }

            // Others done during de-sugaring:
            ast::Block::For(_) | ast::Block::While(_) | ast::Block::If(_) => {
                panic_on_span!(
                    node.span(),
                    "Found non-desugared block in make_term_from_ast_block_expr"
                )
            }
        }
    }

    /// Make a term from an [`ast::BlockExpr`].
    fn make_term_from_ast_block_expr(
        &self,
        node: AstNodeRef<ast::BlockExpr>,
    ) -> SemanticResult<TermId> {
        self.make_term_from_ast_block(node.data.ast_ref())
    }

    /// Make a function term from an AST function definition, which is either a
    /// [`ast::ImplicitFnDef`] or a [`ast::FnDef`].
    fn make_term_from_some_ast_fn_def(
        &self,
        params: AstParams<'_>,
        body: &AstNode<ast::Expr>,
        return_ty: &Option<AstNode<ast::Ty>>,
        node_id: AstNodeId,
    ) -> SemanticResult<TermId> {
        // Function should already be discovered
        let fn_def_id = self.ast_info.fn_defs().get_data_by_node(node_id).unwrap();

        // Whether the function has been marked as pure by a directive
        let is_pure_by_directive = attr_store().node_has_attr(node_id, attrs::PURE);

        let (params, return_ty, return_value, fn_def_id) =
            self.scoping().enter_scope(ContextKind::Environment, || {
                // First resolve the parameters
                let params = self.try_or_add_error(match params {
                    AstParams::Ty(params) => self.resolve_params_from_ast_ty_params(params),
                    AstParams::Param(params) => {
                        self.resolve_params_from_ast_params(params, fn_def_id.borrow().ty.implicit)
                    }
                });

                // Modify the existing fn def for the params:
                if let Some(params) = params {
                    let mut fn_def = fn_def_id.borrow_mut();
                    fn_def.ty.params = params;
                    if is_pure_by_directive {
                        fn_def.ty.pure = true;
                    }
                }

                // In the scope of the parameters, resolve the return type and value
                let return_ty = return_ty.as_ref().map(|return_ty| {
                    self.try_or_add_error(self.make_ty_from_ast_ty(return_ty.ast_ref()))
                });

                // Modify the existing fn def for the return type:
                if let Some(Some(return_ty)) = return_ty {
                    // This is a double option: one for potential error, another for not
                    // specifying return type.
                    fn_def_id.borrow_mut().ty.return_ty = return_ty;
                }

                let return_value =
                    self.try_or_add_error(self.make_term_from_ast_expr(body.ast_ref()));

                // Modify the existing fn def for the return value:
                if let Some(return_value) = return_value {
                    fn_def_id.borrow_mut().body = return_value;
                }

                (params, return_ty, return_value, fn_def_id)
            });

        // If all ok, create a fn ref term
        match (params, return_ty, return_value) {
            (Some(_), None | Some(Some(_)), Some(_)) => {
                Ok(Term::from(Term::Fn(fn_def_id), NodeOrigin::Given(node_id)))
            }
            _ => Err(SemanticError::Signal),
        }
    }

    /// Make a term from an [`ast::ImplicitFnDef`].
    pub(super) fn make_term_from_ast_implicit_fn_def(
        &self,
        node: AstNodeRef<ast::ImplicitFnDef>,
    ) -> SemanticResult<TermId> {
        self.make_term_from_some_ast_fn_def(
            AstParams::Ty(&node.params),
            &node.fn_body,
            &node.return_ty,
            node.id(),
        )
    }

    /// Make a term from an [`ast::FnDef`].
    pub(super) fn make_term_from_ast_fn_def(
        &self,
        node: AstNodeRef<ast::FnDef>,
    ) -> SemanticResult<TermId> {
        self.make_term_from_some_ast_fn_def(
            AstParams::Param(&node.params),
            &node.fn_body,
            &node.return_ty,
            node.id(),
        )
    }

    /// Make a term from an [`ast::AssignOpExpr`].
    fn make_term_from_ast_assign_op_expr(
        &self,
        node: AstNodeRef<ast::AssignOpExpr>,
    ) -> SemanticResult<TermId> {
        // @@Fixme: deal with edge case where LHS has side-effects.
        // We would need to extract the non-projection bit of LHS, assign it to a
        // temporary, and then modify the temporary.
        let subject = self.make_term_from_ast_expr(node.lhs.ast_ref())?;
        let value = self.make_term_from_ast_binary(
            *node.operator.body(),
            node.lhs.ast_ref(),
            node.rhs.ast_ref(),
            NodeOrigin::Given(node.id()),
        )?;
        Ok(Term::from(AssignTerm { subject, value }, NodeOrigin::Given(node.id())))
    }

    /// Make a term from an [`ast::BinaryExpr`].
    fn make_term_from_ast_binary_expr(
        &self,
        node: AstNodeRef<ast::BinaryExpr>,
    ) -> SemanticResult<TermId> {
        self.make_term_from_ast_binary(
            *node.operator.body(),
            node.lhs.ast_ref(),
            node.rhs.ast_ref(),
            NodeOrigin::Given(node.id()),
        )
    }

    /// Make a term from an [`ast::IndexExpr`].
    fn make_term_from_ast_index_expr(
        &self,
        node: AstNodeRef<ast::IndexExpr>,
    ) -> SemanticResult<TermId> {
        let subject = self.make_term_from_ast_expr(node.subject.ast_ref())?;
        let index = self.make_term_from_ast_expr(node.index_expr.ast_ref())?;
        Ok(Term::from(IndexTerm { subject, index }, NodeOrigin::Given(node.id())))
    }

    /// Make a term from an [`ast::RepeatExpr`].
    fn make_term_from_repeat_expr(
        &self,
        node: AstNodeRef<ast::RepeatExpr>,
    ) -> SemanticResult<TermId> {
        let subject = self.make_term_from_ast_expr(node.subject.ast_ref())?;
        let repeat = self.make_term_from_ast_expr(node.repeat.ast_ref())?;
        Ok(Term::from(
            Term::Array(ArrayTerm::Repeated(subject, repeat)),
            NodeOrigin::Given(node.id()),
        ))
    }

    /// Make a term from a binary expression.
    fn make_term_from_ast_binary(
        &self,
        op: ast::BinOp,
        lhs: AstNodeRef<ast::Expr>,
        rhs: AstNodeRef<ast::Expr>,
        origin: NodeOrigin,
    ) -> SemanticResult<TermId> {
        let lhs = self.make_term_from_ast_expr(lhs)?;
        let rhs = self.make_term_from_ast_expr(rhs)?;

        // For the type, we use the type of the lhs
        let typeof_lhs = Term::from(TyOfTerm { term: lhs }, origin);

        // Pick the right intrinsic function and binary operator number
        let (intrinsic, bin_op_num): (Intrinsic, u8) = match op {
            ast::BinOp::EqEq => (Intrinsic::CondBinOp, BinOp::Eq.into()),
            ast::BinOp::NotEq => (Intrinsic::CondBinOp, BinOp::Neq.into()),
            ast::BinOp::BitOr => (Intrinsic::BinOp, BinOp::BitOr.into()),
            ast::BinOp::Or => (Intrinsic::ShortCircuitingBoolOp, LogicalBinOp::Or.into()),
            ast::BinOp::And => (Intrinsic::ShortCircuitingBoolOp, LogicalBinOp::And.into()),
            ast::BinOp::BitAnd => (Intrinsic::BinOp, BinOp::BitAnd.into()),
            ast::BinOp::BitXor => (Intrinsic::BinOp, BinOp::BitXor.into()),
            ast::BinOp::Exp => (Intrinsic::BinOp, BinOp::Exp.into()),
            ast::BinOp::Gt => (Intrinsic::CondBinOp, BinOp::Gt.into()),
            ast::BinOp::GtEq => (Intrinsic::CondBinOp, BinOp::GtEq.into()),
            ast::BinOp::Lt => (Intrinsic::CondBinOp, BinOp::Lt.into()),
            ast::BinOp::LtEq => (Intrinsic::CondBinOp, BinOp::LtEq.into()),
            ast::BinOp::Shr => (Intrinsic::BinOp, BinOp::Shr.into()),
            ast::BinOp::Shl => (Intrinsic::BinOp, BinOp::Shl.into()),
            ast::BinOp::Add => (Intrinsic::BinOp, BinOp::Add.into()),
            ast::BinOp::Sub => (Intrinsic::BinOp, BinOp::Sub.into()),
            ast::BinOp::Mul => (Intrinsic::BinOp, BinOp::Mul.into()),
            ast::BinOp::Div => (Intrinsic::BinOp, BinOp::Div.into()),
            ast::BinOp::Mod => (Intrinsic::BinOp, BinOp::Mod.into()),
            ast::BinOp::As => {
                return Ok(Term::from(AnnotTerm { subject_term: lhs, target_ty: rhs }, origin));
            }
            ast::BinOp::Merge => {
                return Ok(equal_ty(typeof_lhs, lhs, rhs, origin));
            }
        };

        // Invoke the intrinsic function
        Ok(Term::from(
            CallTerm {
                subject: Term::from(intrinsic, origin),
                args: Arg::seq_positional(
                    [typeof_lhs, create_term_from_const(bin_op_num, origin), lhs, rhs],
                    origin,
                ),
                implicit: false,
            },
            origin,
        ))
    }

    /// Make a term from an [`ast::UnaryExpr`].
    fn make_term_from_ast_unary_expr(
        &self,
        node: AstNodeRef<ast::UnaryExpr>,
    ) -> SemanticResult<TermId> {
        let a = self.make_term_from_ast_expr(node.expr.ast_ref())?;
        let origin = NodeOrigin::Given(node.id());
        let typeof_a = Term::from(TyOfTerm { term: a }, origin);

        let (intrinsic, op_num): (Intrinsic, u8) = match node.operator.body() {
            ast::UnOp::BitNot => (Intrinsic::UnOp, UnOp::BitNot.into()),
            ast::UnOp::Not => (Intrinsic::UnOp, UnOp::Not.into()),
            ast::UnOp::Neg => (Intrinsic::UnOp, UnOp::Neg.into()),
        };

        // Invoke the intrinsic function
        Ok(Term::from(
            CallTerm {
                subject: Term::from(intrinsic, origin),
                args: Arg::seq_positional(
                    [typeof_a, create_term_from_const(op_num, origin), a],
                    NodeOrigin::Given(node.id()),
                ),
                implicit: false,
            },
            origin,
        ))
    }
}
