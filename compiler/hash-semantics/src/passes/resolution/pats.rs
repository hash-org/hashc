//! Resolution for patterns.
//!
//! This uses the [super::paths] module to convert AST pattern nodes into
//! TC-patterns. It handles all patterns, but only resolves nested expressions
//! that are paths, using [super::exprs].

use std::iter::empty;

use hash_ast::ast::{self, AstNodeId, AstNodeRef};
use hash_reporting::macros::panic_on_span;
use hash_storage::store::{statics::SequenceStoreValue, SequenceStoreKey};
use hash_tir::{
    args::{PatArg, PatArgsId, PatOrCapture},
    arrays::ArrayPat,
    control::{IfPat, OrPat},
    data::CtorPat,
    intrinsics::utils::bool_pat,
    lits::{CharLit, Lit, LitPat, StrLit},
    node::{Node, NodeId, NodeOrigin},
    params::ParamIndex,
    pats::{Pat, PatId, PatListId, RangePat, Spread},
    scopes::BindingPat,
    symbols::SymbolId,
    tuples::TuplePat,
};

use super::{
    params::AstArgGroup,
    paths::{
        AstPath, AstPathComponent, NonTerminalResolvedPathComponent, ResolvedAstPathComponent,
        TerminalResolvedPathComponent,
    },
    ResolutionPass,
};
use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult},
    env::SemanticEnv,
};

impl<E: SemanticEnv> ResolutionPass<'_, E> {
    /// Make TC pattern arguments from the given set of AST pattern arguments.
    pub(super) fn make_pat_args_from_ast_pat_args(
        &self,
        entries: &ast::AstNodes<ast::PatArg>,
    ) -> SemanticResult<PatArgsId> {
        let args = entries
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                Ok(Node::at(
                    PatArg {
                        target: match arg.name.as_ref() {
                            Some(name) => ParamIndex::Name(name.ident),
                            None => ParamIndex::Position(i),
                        },
                        pat: PatOrCapture::Pat(self.make_pat_from_ast_pat(arg.pat.ast_ref())?),
                    },
                    NodeOrigin::Given(arg.id()),
                ))
            })
            .collect::<SemanticResult<Vec<_>>>()?;
        Ok(Node::create_at(Node::<PatArg>::seq(args), NodeOrigin::Given(entries.id())))
    }

    /// Create a [`PatListId`] from the given [`ast::Pat`]s.
    fn make_pat_list_from_ast_pats(
        &self,
        pats: &ast::AstNodes<ast::Pat>,
    ) -> SemanticResult<PatListId> {
        let created_pats = pats
            .iter()
            .map(|pat| Ok(PatOrCapture::Pat(self.make_pat_from_ast_pat(pat.ast_ref())?)))
            .collect::<SemanticResult<Vec<_>>>()?;
        Ok(Node::create_at(PatOrCapture::seq(created_pats), NodeOrigin::Given(pats.id())))
    }

    /// Create a [`Spread`] from the given [`ast::SpreadPat`].
    ///
    /// This assumes that the current scope already has a binding for the
    /// given name if it is present, and will panic otherwise.
    pub(super) fn make_spread_from_ast_spread(
        &self,
        node: &Option<ast::AstNode<ast::SpreadPat>>,
    ) -> SemanticResult<Option<Spread>> {
        Ok(node.as_ref().map(|node| {
            let symbol = match node.name.as_ref() {
                Some(name) => {
                    self.scoping()
                        .lookup_symbol_by_name_or_error(
                            name.ident,
                            name.id(),
                            self.scoping().get_current_context_kind(),
                        )
                        .unwrap()
                        .0
                }
                None => SymbolId::fresh(NodeOrigin::Given(node.id())),
            };
            Spread { name: symbol, index: node.position }
        }))
    }

    /// Create an [`AstPath`] from the given [`ast::AccessPat`].
    fn access_pat_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::AccessPat>,
    ) -> SemanticResult<AstPath<'a>> {
        match self.pat_as_ast_path(node.body.subject.ast_ref())? {
            Some(mut subject_path) => {
                subject_path.push(AstPathComponent {
                    name: node.property.ident,
                    name_node_id: node.property.id(),
                    args: Node::at(vec![], NodeOrigin::Given(node.id())),
                    node_id: node.id(),
                });
                Ok(subject_path)
            }
            None => Err(SemanticError::InvalidNamespaceSubject { location: node.subject.span() }),
        }
    }

    /// Create an [`AstPath`] from the given [`ast::ConstructorPat`].
    fn constructor_pat_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::ConstructorPat>,
    ) -> SemanticResult<AstPath<'a>> {
        match self.pat_as_ast_path(node.body.subject.ast_ref())? {
            Some(mut path) => match path.last_mut() {
                Some(component) => {
                    component
                        .args
                        .push(AstArgGroup::ExplicitPatArgs(&node.body.fields, &node.body.spread));
                    Ok(path)
                }
                None => panic!("Expected at least one path component"),
            },
            None => Err(SemanticError::InvalidNamespaceSubject { location: node.subject.span() }),
        }
    }

    /// Create an [`AstPath`] from the given [`ast::BindingPat`].
    fn binding_pat_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::BindingPat>,
    ) -> SemanticResult<AstPath<'a>> {
        Ok(vec![AstPathComponent {
            name: node.name.ident,
            name_node_id: node.name.id(),
            args: Node::at(vec![], NodeOrigin::Given(node.id())),
            node_id: node.id(),
        }])
    }

    /// Create an [`AstPath`] from the given [`ast::Pat`].
    fn pat_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::Pat>,
    ) -> SemanticResult<Option<AstPath<'a>>> {
        match node.body {
            ast::Pat::Access(access_pat) => {
                Ok(Some(self.access_pat_as_ast_path(node.with_body(access_pat))?))
            }
            ast::Pat::Constructor(ctor_pat) => {
                Ok(Some(self.constructor_pat_as_ast_path(node.with_body(ctor_pat))?))
            }
            ast::Pat::Binding(binding_pat) => {
                Ok(Some(self.binding_pat_as_ast_path(node.with_body(binding_pat))?))
            }
            ast::Pat::Macro(invocation) => self.pat_as_ast_path(invocation.subject.ast_ref()),
            ast::Pat::Array(_)
            | ast::Pat::Lit(_)
            | ast::Pat::Or(_)
            | ast::Pat::If(_)
            | ast::Pat::Wild(_)
            | ast::Pat::Range(_)
            | ast::Pat::Module(_)
            | ast::Pat::Tuple(_) => Ok(None),
        }
    }

    /// Create a [`PatId`] from the given [`ResolvedAstPathComponent`], or error
    /// if this is not valid.
    fn make_pat_from_resolved_ast_path(
        &self,
        path: &ResolvedAstPathComponent,
        original_node_id: AstNodeId,
    ) -> SemanticResult<PatId> {
        let origin = NodeOrigin::Given(original_node_id);
        match path {
            ResolvedAstPathComponent::NonTerminal(non_terminal) => match non_terminal {
                NonTerminalResolvedPathComponent::Data(_, _) => {
                    // Cannot use a data type in a pattern position
                    Err(SemanticError::CannotUseDataTypeInPatternPosition {
                        location: original_node_id.span(),
                    })
                }
                NonTerminalResolvedPathComponent::Mod(_) => {
                    // Cannot use a module in a pattern position
                    Err(SemanticError::CannotUseModuleInPatternPosition {
                        location: original_node_id.span(),
                    })
                }
            },
            ResolvedAstPathComponent::Terminal(terminal) => match terminal {
                TerminalResolvedPathComponent::CtorPat(ctor_pat) => {
                    // Constructor pattern
                    Ok(Node::create_at(Pat::Ctor(**ctor_pat), origin))
                }
                TerminalResolvedPathComponent::Var(bound_var) => {
                    // Binding pattern
                    // @@Todo: is_mutable, perhaps refactor `BindingPat`?
                    Ok(Node::create_at(
                        Pat::Binding(BindingPat { name: *bound_var, is_mutable: false }),
                        origin,
                    ))
                }
                TerminalResolvedPathComponent::CtorTerm(ctor_term)
                    if ctor_term.ctor_args.is_empty() =>
                {
                    // @@Hack: Constructor term without args is a valid pattern
                    Ok(Node::create_at(
                        Pat::Ctor(CtorPat {
                            ctor: ctor_term.ctor,
                            ctor_pat_args: Node::create_at(
                                Node::<PatArg>::seq(empty()),
                                ctor_term.ctor_args.origin(),
                            ),
                            ctor_pat_args_spread: None,
                            data_args: ctor_term.data_args,
                        }),
                        origin,
                    ))
                }
                TerminalResolvedPathComponent::CtorTerm(_) => {
                    panic_on_span!(
                        original_node_id.span(),
                        "Found constructor term in pattern, expected constructor pattern"
                    )
                }
                TerminalResolvedPathComponent::FnDef(_)
                | TerminalResolvedPathComponent::FnCall(_) => {
                    // Cannot use a function or function call in a pattern position
                    Err(SemanticError::CannotUseFunctionInPatternPosition {
                        location: original_node_id.span(),
                    })
                }
                TerminalResolvedPathComponent::Intrinsic(_) => {
                    Err(SemanticError::CannotUseIntrinsicInPatternPosition {
                        location: original_node_id.span(),
                    })
                }
            },
        }
    }

    /// Create a literal pattern from the given [`ast::Lit`].
    ///
    /// This panics if the given literal is not a valid literal pattern.
    fn make_pat_from_ast_lit(&self, lit_pat: AstNodeRef<ast::Lit>) -> PatId {
        let origin = NodeOrigin::Given(lit_pat.id());
        match lit_pat.body() {
            ast::Lit::Str(str_lit) => Node::create_at(
                Pat::Lit(LitPat(Node::create_at(
                    Lit::Str(StrLit { underlying: *str_lit }),
                    origin,
                ))),
                origin,
            ),
            ast::Lit::Char(char_lit) => Node::create_at(
                Pat::Lit(LitPat(Node::create_at(
                    Lit::Char(CharLit { underlying: *char_lit }),
                    origin,
                ))),
                origin,
            ),
            ast::Lit::Int(int_lit) => Node::create_at(
                Pat::Lit(LitPat(Node::create_at(Lit::Int((*int_lit).into()), origin))),
                origin,
            ),
            ast::Lit::Bool(bool_lit) => bool_pat(bool_lit.data, NodeOrigin::Given(lit_pat.id())),
            ast::Lit::Float(_) | ast::Lit::Array(_) | ast::Lit::Tuple(_) => {
                panic!("Found invalid literal in pattern")
            }
        }
    }

    /// Create a pattern from the given [`ast::Lit`].
    ///
    /// This panics if the given literal is not a valid literal pattern or if it
    /// is a boolean.
    fn make_lit_pat_from_non_bool_ast_lit(&self, lit_pat: AstNodeRef<ast::Lit>) -> LitPat {
        let origin = NodeOrigin::Given(lit_pat.id());
        match lit_pat.body() {
            ast::Lit::Str(str_lit) => {
                LitPat(Node::create_at(Lit::Str(StrLit { underlying: *str_lit }), origin))
            }
            ast::Lit::Char(char_lit) => {
                LitPat(Node::create_at(Lit::Char(CharLit { underlying: *char_lit }), origin))
            }
            ast::Lit::Int(int_lit) => LitPat(Node::create_at(Lit::Int((*int_lit).into()), origin)),
            ast::Lit::Bool(_) | ast::Lit::Float(_) | ast::Lit::Array(_) | ast::Lit::Tuple(_) => {
                panic!("Found invalid literal in pattern")
            }
        }
    }

    /// Create a [`PatId`] from the given [`ast::Pat`], and assign it to the
    /// node in the AST info store.
    ///
    /// This handles all patterns.
    pub(super) fn make_pat_from_ast_pat(
        &self,
        node: AstNodeRef<ast::Pat>,
    ) -> SemanticResult<PatId> {
        // Maybe it has already been made:
        if let Some(pat_id) = self.ast_info.pats().get_data_by_node(node.id()) {
            return Ok(pat_id);
        }
        let origin = NodeOrigin::Given(node.id());

        let pat_id = match node.body {
            ast::Pat::Access(access_pat) => {
                let path = self.access_pat_as_ast_path(node.with_body(access_pat))?;
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_pat_from_resolved_ast_path(&resolved_path, node.id())?
            }
            ast::Pat::Binding(binding_pat) => {
                let path = self.binding_pat_as_ast_path(node.with_body(binding_pat))?;
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_pat_from_resolved_ast_path(&resolved_path, node.id())?
            }
            ast::Pat::Constructor(ctor_pat) => {
                let path = self.constructor_pat_as_ast_path(node.with_body(ctor_pat))?;
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_pat_from_resolved_ast_path(&resolved_path, node.id())?
            }
            ast::Pat::Macro(invocation) => {
                return self.make_pat_from_ast_pat(invocation.subject.ast_ref())
            }
            ast::Pat::Module(_) => {
                // This should be handled earlier
                panic_on_span!(node.span(), "Found module pattern during symbol resolution")
            }
            ast::Pat::Tuple(tuple_pat) => Node::create_at(
                Pat::Tuple(TuplePat {
                    data: self.make_pat_args_from_ast_pat_args(&tuple_pat.fields)?,
                    data_spread: self.make_spread_from_ast_spread(&tuple_pat.spread)?,
                }),
                origin,
            ),
            ast::Pat::Array(array_pat) => Node::create_at(
                Pat::Array(ArrayPat {
                    pats: self.make_pat_list_from_ast_pats(&array_pat.fields)?,
                    spread: self.make_spread_from_ast_spread(&array_pat.spread)?,
                }),
                origin,
            ),
            ast::Pat::Lit(lit_pat) => self.make_pat_from_ast_lit(lit_pat.data.ast_ref()),
            ast::Pat::Or(or_pat) => Node::create_at(
                Pat::Or(OrPat {
                    alternatives: self.make_pat_list_from_ast_pats(&or_pat.variants)?,
                }),
                origin,
            ),
            ast::Pat::If(if_pat) => Node::create_at(
                Pat::If(IfPat {
                    condition: self.make_term_from_ast_expr(if_pat.condition.ast_ref())?,
                    pat: self.make_pat_from_ast_pat(if_pat.pat.ast_ref())?,
                }),
                origin,
            ),
            ast::Pat::Wild(_) => Node::create_at(
                Pat::Binding(BindingPat {
                    name: SymbolId::fresh(NodeOrigin::Given(node.id())),
                    is_mutable: false,
                }),
                origin,
            ),
            ast::Pat::Range(ast::RangePat { lo, hi, end }) => {
                let lo =
                    lo.as_ref().map(|lo| self.make_lit_pat_from_non_bool_ast_lit(lo.ast_ref()));
                let hi =
                    hi.as_ref().map(|hi| self.make_lit_pat_from_non_bool_ast_lit(hi.ast_ref()));
                Node::create_at(Pat::Range(RangePat { lo, hi, end: *end }), origin)
            }
        };

        self.ast_info.pats().insert(node.id(), pat_id);
        Ok(pat_id)
    }
}
