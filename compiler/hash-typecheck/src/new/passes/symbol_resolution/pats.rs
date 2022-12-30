use hash_ast::ast::{self, AstNodeRef};
use hash_types::new::{
    args::{PatArgData, PatArgsId},
    control::{IfPat, OrPat},
    environment::env::AccessToEnv,
    lits::{CharLit, IntLit, LitPat, StrLit},
    params::ParamTarget,
    pats::{ListPat, Pat, PatId, PatListId, Spread},
    tuples::TuplePat,
};
use hash_utils::store::{CloneStore, SequenceStore};

use super::{
    ast_paths::{AstArgGroup, AstPath, AstPathComponent},
    SymbolResolutionPass,
};
use crate::new::{
    diagnostics::error::{TcError, TcResult},
    ops::{ast::AstOps, common::CommonOps, AccessToOps},
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

    /// Create a [`PatId`] from the given [`ast::Pat`].
    pub fn make_pat_from_ast_pat(&self, node: AstNodeRef<ast::Pat>) -> TcResult<PatId> {
        match node.body {
            ast::Pat::Access(_access_pat) => {
                // let path = self.access_pat_as_ast_path(node.with_body(access_pat))?;
                todo!()
            }
            ast::Pat::Binding(_) => todo!(),
            ast::Pat::Constructor(_) => todo!(),
            ast::Pat::Module(_) => todo!(),
            ast::Pat::Tuple(tuple_pat) => Ok(self.new_pat(Pat::Tuple(TuplePat {
                data: self.ast_tuple_pat_entries_as_pat_args(&tuple_pat.fields)?,
                original_ty: None,
                data_spread: self.ast_spread_as_spread(&tuple_pat.spread)?,
            }))),
            ast::Pat::List(list_pat) => Ok(self.new_pat(Pat::List(ListPat {
                pats: self.ast_pats_as_pat_list(&list_pat.fields)?,
                spread: self.ast_spread_as_spread(&list_pat.spread)?,
            }))),
            ast::Pat::Lit(lit_pat) => match lit_pat.data.body() {
                ast::Lit::Str(str_lit) => {
                    Ok(self.new_pat(Pat::Lit(LitPat::Str(StrLit { underlying: *str_lit }))))
                }
                ast::Lit::Char(char_lit) => {
                    Ok(self.new_pat(Pat::Lit(LitPat::Char(CharLit { underlying: *char_lit }))))
                }
                ast::Lit::Int(int_lit) => {
                    Ok(self.new_pat(Pat::Lit(LitPat::Int(IntLit { underlying: *int_lit }))))
                }
                ast::Lit::Bool(_bool_lit) => {
                    // @@Todo: bool constructor
                    todo!()
                }
                ast::Lit::Float(_)
                | ast::Lit::Set(_)
                | ast::Lit::Map(_)
                | ast::Lit::List(_)
                | ast::Lit::Tuple(_) => panic!("Found invalid literal in pattern"),
            },
            ast::Pat::Or(or_pat) => Ok(self.new_pat(Pat::Or(OrPat {
                alternatives: self.ast_pats_as_pat_list(&or_pat.variants)?,
            }))),
            ast::Pat::If(if_pat) => Ok(self.new_pat(Pat::If(IfPat {
                condition: self.new_term_hole(), // @@Todo: queue up a term to be resolved
                pat: self.make_pat_from_ast_pat(if_pat.pat.ast_ref())?,
            }))),
            ast::Pat::Wild(_) => todo!(),
            ast::Pat::Range(_) => todo!(),
        }
    }

    /// Create an [`AstPath`] from the given [`ast::AccessPat`].
    fn access_pat_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::AccessPat>,
    ) -> TcResult<AstPath<'a>> {
        match self.ast_pat_as_ast_path(node.body.subject.ast_ref())? {
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
        match self.ast_pat_as_ast_path(node.body.subject.ast_ref())? {
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
    fn ast_pat_as_ast_path<'a>(
        &self,
        node: AstNodeRef<'a, ast::Pat>,
    ) -> TcResult<Option<AstPath<'a>>> {
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
}
