//! Resolution for patterns.
//!
//! This uses the [super::paths] module to convert AST pattern nodes into
//! TC-patterns. It handles all patterns, but only resolves nested expressions
//! that are paths, using [super::exprs].

use std::iter::empty;

use hash_ast::ast::{self, AstNodeRef};
use hash_reporting::macros::panic_on_span;
use hash_source::location::Span;
use hash_tir::new::{
    args::{PatArgData, PatArgsId},
    control::{IfPat, OrPat},
    data::CtorPat,
    environment::env::AccessToEnv,
    lits::{CharLit, IntLit, ListPat, LitPat, StrLit},
    params::ParamIndex,
    pats::{Pat, PatId, PatListId, RangePat, Spread},
    scopes::BindingPat,
    tuples::TuplePat,
    utils::{common::CommonUtils, AccessToUtils},
};
use hash_utils::store::{SequenceStore, SequenceStoreKey};

use super::{
    params::AstArgGroup,
    paths::{
        AstPath, AstPathComponent, NonTerminalResolvedPathComponent, ResolvedAstPathComponent,
        TerminalResolvedPathComponent,
    },
    ResolutionPass,
};
use crate::new::{
    diagnostics::error::{SemanticError, SemanticResult},
    environment::tc_env::AccessToTcEnv,
    passes::ast_utils::AstUtils,
};

impl ResolutionPass<'_> {
    /// Make TC pattern arguments from the given set of AST pattern arguments.
    pub(super) fn make_pat_args_from_ast_pat_args(
        &self,
        entries: &ast::AstNodes<ast::TuplePatEntry>,
    ) -> SemanticResult<PatArgsId> {
        let args = entries
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                Ok(PatArgData {
                    target: match arg.name.as_ref() {
                        Some(name) => ParamIndex::Name(name.ident),
                        None => ParamIndex::Position(i),
                    },
                    pat: self.make_pat_from_ast_pat(arg.pat.ast_ref())?,
                })
            })
            .collect::<SemanticResult<Vec<_>>>()?;
        Ok(self.param_utils().create_pat_args(args.into_iter()))
    }

    /// Create a [`PatListId`] from the given [`ast::Pat`]s.
    fn make_pat_list_from_ast_pats(
        &self,
        pats: &ast::AstNodes<ast::Pat>,
    ) -> SemanticResult<PatListId> {
        let pats = pats
            .iter()
            .map(|pat| self.make_pat_from_ast_pat(pat.ast_ref()))
            .collect::<SemanticResult<Vec<_>>>()?;
        Ok(self.stores().pat_list().create_from_iter_fast(pats.into_iter()))
    }

    /// Create a [`Spread`] from the given [`ast::SpreadPat`].
    ///
    /// This assumes that the current scope already has a binding for the
    /// given name if it is present, and will panic otherwise.
    pub(super) fn make_spread_from_ast_spread(
        &self,
        node: &Option<ast::AstNode<ast::SpreadPat>>,
    ) -> SemanticResult<Option<Spread>> {
        Ok(node.as_ref().map(|node| Spread {
            name: node
                .name
                .as_ref()
                .map(|name| self.scoping().lookup_symbol_by_name(name.ident).unwrap())
                .unwrap_or_else(|| self.new_fresh_symbol()),
            index: node.position,
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
                    name_span: node.property.span(),
                    args: vec![],
                    node_id: node.id(),
                });
                Ok(subject_path)
            }
            None => Err(SemanticError::InvalidNamespaceSubject {
                location: self.node_location(node.subject.ast_ref()),
            }),
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
            None => Err(SemanticError::InvalidNamespaceSubject {
                location: self.node_location(node.subject.ast_ref()),
            }),
        }
    }

    /// Create an [`AstPath`] from the given [`ast::BindingPat`].
    fn binding_pat_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::BindingPat>,
    ) -> SemanticResult<AstPath<'a>> {
        Ok(vec![AstPathComponent {
            name: node.name.ident,
            name_span: node.name.span(),
            args: vec![],
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
    ) -> SemanticResult<PatId> {
        match path {
            ResolvedAstPathComponent::NonTerminal(non_terminal) => match non_terminal {
                NonTerminalResolvedPathComponent::Data(_, _) => {
                    // Cannot use a data type in a pattern position
                    Err(SemanticError::CannotUseDataTypeInPatternPosition {
                        location: self.source_location(original_node_span),
                    })
                }
                NonTerminalResolvedPathComponent::Mod(_) => {
                    // Cannot use a module in a pattern position
                    Err(SemanticError::CannotUseModuleInPatternPosition {
                        location: self.source_location(original_node_span),
                    })
                }
            },
            ResolvedAstPathComponent::Terminal(terminal) => match terminal {
                TerminalResolvedPathComponent::CtorPat(ctor_pat) => {
                    // Constructor pattern
                    Ok(self.new_pat(Pat::Ctor(*ctor_pat)))
                }
                TerminalResolvedPathComponent::Var(bound_var) => {
                    // Binding pattern
                    // @@Todo: is_mutable, perhaps refactor `BindingPat`?
                    Ok(self.new_pat(Pat::Binding(BindingPat {
                        name: bound_var.name,
                        is_mutable: false,
                    })))
                }
                TerminalResolvedPathComponent::CtorTerm(ctor_term)
                    if ctor_term.ctor_args.is_empty() =>
                {
                    // @@Hack: Constructor term without args is a valid pattern
                    Ok(self.new_pat(Pat::Ctor(CtorPat {
                        ctor: ctor_term.ctor,
                        ctor_pat_args: self.param_utils().create_def_pat_args(empty()),
                        data_args: ctor_term.data_args,
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
                    Err(SemanticError::CannotUseFunctionInPatternPosition {
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
    pub(super) fn make_pat_from_ast_pat(
        &self,
        node: AstNodeRef<ast::Pat>,
    ) -> SemanticResult<PatId> {
        // Maybe it has already been made:
        if let Some(pat_id) = self.ast_info().pats().get_data_by_node(node.id()) {
            return Ok(pat_id);
        }

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
                data: self.make_pat_args_from_ast_pat_args(&tuple_pat.fields)?,
                original_ty: None,
                data_spread: self.make_spread_from_ast_spread(&tuple_pat.spread)?,
            })),
            ast::Pat::List(list_pat) => self.new_pat(Pat::List(ListPat {
                pats: self.make_pat_list_from_ast_pats(&list_pat.fields)?,
                spread: self.make_spread_from_ast_spread(&list_pat.spread)?,
            })),
            ast::Pat::Lit(lit_pat) => {
                self.new_pat(Pat::Lit(self.make_lit_pat_from_ast_lit(lit_pat.data.ast_ref())))
            }
            ast::Pat::Or(or_pat) => self.new_pat(Pat::Or(OrPat {
                alternatives: self.make_pat_list_from_ast_pats(&or_pat.variants)?,
            })),
            ast::Pat::If(if_pat) => self.new_pat(Pat::If(IfPat {
                condition: self.make_term_from_ast_expr(if_pat.condition.ast_ref())?,
                pat: self.make_pat_from_ast_pat(if_pat.pat.ast_ref())?,
            })),
            ast::Pat::Wild(_) => self.new_pat(Pat::Binding(BindingPat {
                name: self.new_symbol("_"),
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
