//! Path-resolution for patterns.
//!
//! This uses the [super::paths] module to convert AST pattern nodes into
//! TC-patterns. It handles all patterns, but only resolves nested expressions
//! that are paths, using [super::exprs].

use hash_ast::ast::{self, AstNodeRef};
use hash_reporting::macros::panic_on_span;
use hash_source::location::Span;
use hash_types::new::{
    args::{PatArgData, PatArgsId},
    control::{IfPat, OrPat},
    environment::env::AccessToEnv,
    lits::{CharLit, IntLit, LitPat, StrLit},
    params::ParamTarget,
    pats::{ListPat, Pat, PatId, PatListId, RangePat, Spread},
    scopes::BindingPat,
    tuples::TuplePat,
};
use hash_utils::store::SequenceStore;

use super::{
    paths::{
        AstArgGroup, AstPath, AstPathComponent, NonTerminalResolvedPathComponent,
        ResolvedAstPathComponent, TerminalResolvedPathComponent,
    },
    SymbolResolutionPass,
};
use crate::new::{
    diagnostics::error::{TcError, TcResult},
    environment::tc_env::AccessToTcEnv,
    ops::{common::CommonOps, AccessToOps},
    passes::ast_pass::AstPass,
};

impl SymbolResolutionPass<'_> {
    /// Create a [`PatArgsId`] from the given [`ast::TuplePatEntry`]s.
    fn ast_tuple_pat_entries_as_pat_args(
        &self,
        entries: &ast::AstNodes<ast::TuplePatEntry>,
    ) -> TcResult<PatArgsId> {
        let args = entries
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                Ok(PatArgData {
                    target: match arg.name.as_ref() {
                        Some(name) => ParamTarget::Name(name.ident),
                        None => ParamTarget::Position(i),
                    },
                    pat: self.make_pat_from_ast_pat(arg.pat.ast_ref())?,
                })
            })
            .collect::<TcResult<Vec<_>>>()?;
        Ok(self.param_ops().create_pat_args(args.into_iter()))
    }

    /// Create a [`PatListId`] from the given [`ast::Pat`]s.
    fn ast_pats_as_pat_list(&self, pats: &ast::AstNodes<ast::Pat>) -> TcResult<PatListId> {
        let pats = pats
            .iter()
            .map(|pat| self.make_pat_from_ast_pat(pat.ast_ref()))
            .collect::<TcResult<Vec<_>>>()?;
        Ok(self.stores().pat_list().create_from_iter_fast(pats.into_iter()))
    }

    /// Create a [`Spread`] from the given [`ast::SpreadPat`].
    fn ast_spread_as_spread(
        &self,
        _node: &Option<ast::AstNode<ast::SpreadPat>>,
    ) -> TcResult<Option<Spread>> {
        todo!()
    }

    /// Create an [`AstPath`] from the given [`ast::AccessPat`].
    fn access_pat_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::AccessPat>,
    ) -> TcResult<AstPath<'a>> {
        match self.pat_as_ast_path(node.body.subject.ast_ref())? {
            Some(mut subject_path) => {
                subject_path.push(AstPathComponent {
                    name: node.property.ident,
                    name_span: node.property.span(),
                    args: vec![],
                    node_id: node.id(),
                });
                Ok(subject_path)
            }
            None => Err(TcError::InvalidNamespaceSubject {
                location: self.node_location(node.subject.ast_ref()),
            }),
        }
    }

    /// Create an [`AstPath`] from the given [`ast::ConstructorPat`].
    fn constructor_pat_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::ConstructorPat>,
    ) -> TcResult<AstPath<'a>> {
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
            None => Err(TcError::InvalidNamespaceSubject {
                location: self.node_location(node.subject.ast_ref()),
            }),
        }
    }

    /// Create an [`AstPath`] from the given [`ast::BindingPat`].
    fn binding_pat_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::BindingPat>,
    ) -> TcResult<AstPath<'a>> {
        Ok(vec![AstPathComponent {
            name: node.name.ident,
            name_span: node.name.span(),
            args: vec![],
            node_id: node.id(),
        }])
    }

    /// Create an [`AstPath`] from the given [`ast::Pat`].
    fn pat_as_ast_path<'a>(&self, node: AstNodeRef<'a, ast::Pat>) -> TcResult<Option<AstPath<'a>>> {
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
            ast::Pat::List(_)
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
        original_node_span: Span,
    ) -> TcResult<PatId> {
        match path {
            ResolvedAstPathComponent::NonTerminal(non_terminal) => match non_terminal {
                NonTerminalResolvedPathComponent::Data(_, _) => {
                    // Cannot use a data type in a pattern position
                    Err(TcError::CannotUseDataTypeInPatternPosition {
                        location: self.source_location(original_node_span),
                    })
                }
                NonTerminalResolvedPathComponent::Mod(_, _) => {
                    // Cannot use a module in a pattern position
                    Err(TcError::CannotUseModuleInPatternPosition {
                        location: self.source_location(original_node_span),
                    })
                }
            },
            ResolvedAstPathComponent::Terminal(terminal) => match terminal {
                TerminalResolvedPathComponent::CtorPat(ctor_pat) => {
                    // Constructor pattern
                    Ok(self.new_pat(Pat::Ctor(*ctor_pat)))
                }
                TerminalResolvedPathComponent::BoundVar(bound_var) => {
                    // Binding pattern
                    // @@Todo: is_mutable, perhaps refactor `BindingPat`?
                    Ok(self.new_pat(Pat::Binding(BindingPat {
                        name: bound_var.name,
                        is_mutable: false,
                    })))
                }
                TerminalResolvedPathComponent::CtorTerm(_) => {
                    panic_on_span!(
                        self.source_location(original_node_span),
                        self.source_map(),
                        "Found constructor term in pattern, expected constructor pattern"
                    )
                }
                TerminalResolvedPathComponent::FnDef(_)
                | TerminalResolvedPathComponent::FnCall(_) => {
                    // Cannot use a function or function call in a pattern position
                    Err(TcError::CannotUseFunctionInPatternPosition {
                        location: self.source_location(original_node_span),
                    })
                }
            },
        }
    }

    /// Create a literal pattern from the given [`ast::Lit`].
    ///
    /// This panics if the given literal is not a valid literal pattern.
    fn make_lit_pat_from_ast_lit(&self, lit_pat: AstNodeRef<ast::Lit>) -> LitPat {
        match lit_pat.body() {
            ast::Lit::Str(str_lit) => LitPat::Str(StrLit { underlying: *str_lit }),
            ast::Lit::Char(char_lit) => LitPat::Char(CharLit { underlying: *char_lit }),
            ast::Lit::Int(int_lit) => LitPat::Int(IntLit { underlying: *int_lit }),
            ast::Lit::Bool(_bool_lit) => {
                // @@Todo: bool constructor
                todo!("Bool patterns currently not implemented")
            }
            ast::Lit::Float(_)
            | ast::Lit::Set(_)
            | ast::Lit::Map(_)
            | ast::Lit::List(_)
            | ast::Lit::Tuple(_) => panic!("Found invalid literal in pattern"),
        }
    }

    /// Create a [`PatId`] from the given [`ast::Pat`], and assign it to the
    /// node in the AST info store.
    ///
    /// This handles all patterns.
    pub fn make_pat_from_ast_pat(&self, node: AstNodeRef<ast::Pat>) -> TcResult<PatId> {
        let pat_id = match node.body {
            ast::Pat::Access(access_pat) => {
                let path = self.access_pat_as_ast_path(node.with_body(access_pat))?;
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_pat_from_resolved_ast_path(&resolved_path, node.span())?
            }
            ast::Pat::Binding(binding_pat) => {
                let path = self.binding_pat_as_ast_path(node.with_body(binding_pat))?;
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_pat_from_resolved_ast_path(&resolved_path, node.span())?
            }
            ast::Pat::Constructor(ctor_pat) => {
                let path = self.constructor_pat_as_ast_path(node.with_body(ctor_pat))?;
                let resolved_path = self.resolve_ast_path(&path)?;
                self.make_pat_from_resolved_ast_path(&resolved_path, node.span())?
            }
            ast::Pat::Module(_) => {
                // This should be handled earlier
                panic_on_span!(
                    self.source_location(node.span()),
                    self.source_map(),
                    "Found module pattern during symbol resolution"
                )
            }
            ast::Pat::Tuple(tuple_pat) => self.new_pat(Pat::Tuple(TuplePat {
                data: self.ast_tuple_pat_entries_as_pat_args(&tuple_pat.fields)?,
                original_ty: None,
                data_spread: self.ast_spread_as_spread(&tuple_pat.spread)?,
            })),
            ast::Pat::List(list_pat) => self.new_pat(Pat::List(ListPat {
                pats: self.ast_pats_as_pat_list(&list_pat.fields)?,
                spread: self.ast_spread_as_spread(&list_pat.spread)?,
            })),
            ast::Pat::Lit(lit_pat) => {
                self.new_pat(Pat::Lit(self.make_lit_pat_from_ast_lit(lit_pat.data.ast_ref())))
            }
            ast::Pat::Or(or_pat) => self.new_pat(Pat::Or(OrPat {
                alternatives: self.ast_pats_as_pat_list(&or_pat.variants)?,
            })),
            ast::Pat::If(if_pat) => self.new_pat(Pat::If(IfPat {
                condition: self.make_term_from_ast_expr(if_pat.condition.ast_ref())?,
                pat: self.make_pat_from_ast_pat(if_pat.pat.ast_ref())?,
            })),
            ast::Pat::Wild(_) => self.new_pat(Pat::Binding(BindingPat {
                name: self.new_fresh_symbol(),
                is_mutable: false,
            })),
            ast::Pat::Range(range_pat) => {
                let start = self.make_lit_pat_from_ast_lit(range_pat.lo.ast_ref());
                let end = self.make_lit_pat_from_ast_lit(range_pat.hi.ast_ref());
                self.new_pat(Pat::Range(RangePat { start, end, range_end: range_pat.end }))
            }
        };

        self.ast_info().pats().insert(node.id(), pat_id);
        Ok(pat_id)
    }
}
