//! Resolution of item paths in the AST.
//!
//! An item path is something that follows the grammar:
//!
//! ```notrust
//! path ::= path_component ( "::" path_component )
//! path_component ::= identifier ( ( "<" args ">" ) | ( "(" args ")" ) )*
//! ```
//! where `args` are type args, expr args, or pattern args.
//!
//! Paths in the AST can be resolved to a number of different things:
//! - Types: Data types, function calls
//! - Terms: Functions, function calls, constructors
//! - Patterns: Constructors
//!
//! This module contains the [`AstPath`] type, which is used to represent paths
//! in the AST before they are resolved. The [`ResolvedAstPathComponent`] type
//! is used to represent a path or path component after it has been resolved.
//! This can then be used to create a term, type, or pattern, with appropriate
//! restrictions on the arguments and item kind.

use std::fmt;

use hash_ast::ast;
use hash_source::{identifier::Identifier, location::Span};
use hash_storage::store::{statics::StoreId, TrivialKeySequenceStore};
use hash_tir::{
    args::ArgsId,
    data::{CtorPat, CtorTerm, DataDefId},
    environment::env::AccessToEnv,
    fns::{FnCallTerm, FnDefId},
    mods::{ModDefId, ModMemberValue},
    symbols::Symbol,
    terms::Term,
    utils::common::CommonUtils,
};

use super::{
    params::{AstArgGroup, ResolvedArgs},
    scoping::{BindingKind, ContextKind},
    ResolutionPass,
};
use crate::diagnostics::error::{SemanticError, SemanticResult};

/// A path component in the AST.
///
/// A path is a sequence of path components, separated by `::`.
/// A path component is either a name, or a name followed by a list of
/// argument groups, each of which is a [`AstArgGroup`].
///
/// For example: `Foo::Bar::Baz<T, U>(a, b, c)::Bin(3)`.
#[derive(Clone, Debug)]
pub struct AstPathComponent<'a> {
    pub name: Identifier,
    pub name_span: Span,
    pub args: Vec<AstArgGroup<'a>>,
    pub node_id: ast::AstNodeId,
}

/// A path in the AST.
///
/// For example, `Foo::Bar`.
pub type AstPath<'a> = Vec<AstPathComponent<'a>>;

impl AstPathComponent<'_> {
    /// Get the span of this path component.
    pub fn span(&self) -> Span {
        let span = self.name_span;
        if let Some(last_arg) = self.args.last() {
            span.join(last_arg.span())
        } else {
            span
        }
    }
}

/// A non-terminal resolved path component in the AST.
///
/// This is a path component that has been resolved to a non-terminal item,
/// which means that it can be accessed further through `::`.
#[derive(Clone, Copy, Debug)]
pub enum NonTerminalResolvedPathComponent {
    /// A data definition with some arguments.
    Data(DataDefId, ArgsId),
    /// A module definition.
    Mod(ModDefId),
}

/// Each non-terminal resolved path component is a module member.
impl From<NonTerminalResolvedPathComponent> for ModMemberValue {
    fn from(value: NonTerminalResolvedPathComponent) -> Self {
        match value {
            NonTerminalResolvedPathComponent::Data(data_def_id, _) => {
                ModMemberValue::Data(data_def_id)
            }
            NonTerminalResolvedPathComponent::Mod(mod_def_id) => ModMemberValue::Mod(mod_def_id),
        }
    }
}

impl fmt::Display for NonTerminalResolvedPathComponent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ModMemberValue::from(*self).name())
    }
}

/// A terminal resolved path component in the AST.
///
/// This is a path component that has been resolved to a terminal item,
/// which means that it cannot be accessed further through `::`.
#[derive(Clone, Copy, Debug)]
pub enum TerminalResolvedPathComponent {
    /// A function reference.
    FnDef(FnDefId),
    /// A data constructor pattern.
    CtorPat(CtorPat),
    /// A data constructor term.
    CtorTerm(CtorTerm),
    /// A function call term.
    FnCall(FnCallTerm),
    /// A variable bound in the current context.
    Var(Symbol),
}

/// The result of resolving a path component.
///
/// This is either a non-terminal resolved path component, or a terminal
/// resolved path component.
#[derive(Clone, Copy, Debug)]
pub enum ResolvedAstPathComponent {
    NonTerminal(NonTerminalResolvedPathComponent),
    Terminal(TerminalResolvedPathComponent),
}

/// This block performs resolution of AST paths.
impl<'tc> ResolutionPass<'tc> {
    /// Resolve a name starting from the given [`ModMemberValue`], or the
    /// current context if no such value is given.
    ///
    /// Returns the binding that the name resolves to.
    fn resolve_ast_name(
        &self,
        name: Identifier,
        name_span: Span,
        starting_from: Option<(NonTerminalResolvedPathComponent, Span)>,
    ) -> SemanticResult<(Symbol, BindingKind)> {
        match starting_from {
            Some((member_value, _span)) => match member_value {
                // If we are starting from a module or data type, we need to enter their scopes.
                NonTerminalResolvedPathComponent::Data(data_def_id, _def_args_id) => self
                    .scoping()
                    .enter_scope(ContextKind::Access(member_value, data_def_id.into()), || {
                        self.scoping().add_data_params_and_ctors(data_def_id);
                        self.resolve_ast_name(name, name_span, None)
                    }),
                NonTerminalResolvedPathComponent::Mod(mod_def_id) => self.scoping().enter_scope(
                    ContextKind::Access(member_value, mod_def_id.into()),
                    || {
                        self.scoping().add_mod_members(mod_def_id);
                        self.resolve_ast_name(name, name_span, None)
                    },
                ),
            },
            None => {
                // If there is no start point, try to lookup the variable in the current scope.
                self.scoping().lookup_symbol_by_name_or_error(
                    name,
                    name_span,
                    self.scoping().get_current_context_kind(),
                )
            }
        }
    }

    /// Resolve a path component, starting from the given
    /// [`NonTerminalResolvedPathComponent`] if present, or the current
    /// context if not.
    ///
    /// Returns a [`ResolvedAstPathComponent`] which might or might not support
    /// further accessing depending on the variant.
    fn resolve_ast_path_component(
        &self,
        component: &AstPathComponent<'_>,
        starting_from: Option<(NonTerminalResolvedPathComponent, Span)>,
    ) -> SemanticResult<ResolvedAstPathComponent> {
        let (_binding, binding_kind) =
            self.resolve_ast_name(component.name, component.name_span, starting_from)?;

        match binding_kind {
            BindingKind::ModMember(_, mod_member_id) => {
                let mod_member = self.stores().mod_members().get_element(mod_member_id);
                match mod_member.value {
                    ModMemberValue::Data(data_def_id) => {
                        let data_def_single_ctor = data_def_id.borrow().get_single_ctor();

                        let (data_args, ctor_args): (ResolvedArgs, Option<ResolvedArgs>) =
                            match &component.args[..] {
                                [] => (ResolvedArgs::Term(self.new_empty_args()), None),
                                [arg_group] if arg_group.is_implicit() => {
                                    (self.make_args_from_ast_arg_group(arg_group)?, None)
                                }
                                [arg_group] => {
                                    assert!(!arg_group.is_implicit());
                                    (
                                        ResolvedArgs::Term(self.new_empty_args()),
                                        Some(self.make_args_from_ast_arg_group(arg_group)?),
                                    )
                                }
                                [data_arg_group, ctor_arg_group]
                                    if data_arg_group.is_implicit()
                                        && !ctor_arg_group.is_implicit() =>
                                {
                                    (
                                        (self.make_args_from_ast_arg_group(data_arg_group)?),
                                        Some(self.make_args_from_ast_arg_group(ctor_arg_group)?),
                                    )
                                }
                                [first, second, _rest @ ..] => {
                                    return Err(SemanticError::UnexpectedArguments {
                                        location: first.span().join(second.span()),
                                    });
                                }
                            };

                        match (data_args, ctor_args) {
                            (ResolvedArgs::Term(args), None) => {
                                Ok(ResolvedAstPathComponent::NonTerminal(
                                    NonTerminalResolvedPathComponent::Data(data_def_id, args),
                                ))
                            }
                            (
                                ResolvedArgs::Term(data_args),
                                Some(ResolvedArgs::Pat(ctor_pat_args, ctor_pat_args_spread)),
                            ) => match data_def_single_ctor {
                                Some(ctor) => Ok(ResolvedAstPathComponent::Terminal(
                                    TerminalResolvedPathComponent::CtorPat(CtorPat {
                                        ctor: ctor.id,
                                        data_args,
                                        ctor_pat_args,
                                        ctor_pat_args_spread,
                                    }),
                                )),
                                None => Err(SemanticError::DataDefIsNotSingleton {
                                    location: component.name_span,
                                }),
                            },
                            (
                                ResolvedArgs::Term(data_args),
                                Some(ResolvedArgs::Term(ctor_args)),
                            ) => match data_def_single_ctor {
                                Some(ctor) => Ok(ResolvedAstPathComponent::Terminal(
                                    TerminalResolvedPathComponent::CtorTerm(CtorTerm {
                                        ctor: ctor.id,
                                        data_args,
                                        ctor_args,
                                    }),
                                )),
                                None => Err(SemanticError::DataDefIsNotSingleton {
                                    location: component.name_span,
                                }),
                            },
                            (ResolvedArgs::Pat(_, _), _) => {
                                Err(SemanticError::CannotUseDataTypeInPatternPosition {
                                    location: component.name_span,
                                })
                            }
                        }
                    }
                    ModMemberValue::Mod(mod_def_id) => Ok(ResolvedAstPathComponent::NonTerminal(
                        NonTerminalResolvedPathComponent::Mod(mod_def_id),
                    )),
                    ModMemberValue::Fn(fn_def_id) => match &component.args[..] {
                        [] => Ok(ResolvedAstPathComponent::Terminal(
                            TerminalResolvedPathComponent::FnDef(fn_def_id),
                        )),
                        args => {
                            let resultant_term = self.wrap_term_in_fn_call_from_ast_args(
                                self.new_term(Term::FnRef(fn_def_id)),
                                args,
                                component.span(),
                            )?;
                            Ok(ResolvedAstPathComponent::Terminal(
                                TerminalResolvedPathComponent::FnCall(resultant_term),
                            ))
                        }
                    },
                }
            }
            BindingKind::Ctor(data_def_id, ctor_def_id) => {
                let _ctor_def = self.stores().ctor_defs().get_element(ctor_def_id);
                let applied_args = match &component.args[..] {
                    [] => ResolvedArgs::Term(self.new_empty_args()),
                    [arg_group] => self.make_args_from_ast_arg_group(arg_group)?,
                    [_first, second, _rest @ ..] => {
                        return Err(SemanticError::UnexpectedArguments { location: second.span() });
                    }
                };

                match starting_from {
                    Some((starting_from, _)) => match starting_from {
                        NonTerminalResolvedPathComponent::Data(
                            starting_from_data_def_id,
                            data_args,
                        ) => {
                            assert!(starting_from_data_def_id == data_def_id);
                            match applied_args {
                                ResolvedArgs::Term(ctor_args) => {
                                    Ok(ResolvedAstPathComponent::Terminal(
                                        TerminalResolvedPathComponent::CtorTerm(CtorTerm {
                                            ctor: ctor_def_id,
                                            ctor_args,
                                            data_args,
                                        }),
                                    ))
                                }
                                ResolvedArgs::Pat(ctor_pat_args, spread) => {
                                    Ok(ResolvedAstPathComponent::Terminal(
                                        TerminalResolvedPathComponent::CtorPat(CtorPat {
                                            ctor: ctor_def_id,
                                            ctor_pat_args,
                                            data_args,
                                            ctor_pat_args_spread: spread,
                                        }),
                                    ))
                                }
                            }
                        }

                        NonTerminalResolvedPathComponent::Mod(_) => {
                            unreachable!("Can never have a constructor starting from a module")
                        }
                    },
                    None => unreachable!(),
                }
            }
            BindingKind::Sym(decl) => {
                // If the subject has no args, it is a variable, otherwise it is a
                // function call.
                match &component.args[..] {
                    [] => Ok(ResolvedAstPathComponent::Terminal(
                        TerminalResolvedPathComponent::Var(decl),
                    )),
                    args => {
                        let resultant_term = self.wrap_term_in_fn_call_from_ast_args(
                            self.new_term(Term::Var(decl)),
                            args,
                            component.span(),
                        )?;
                        Ok(ResolvedAstPathComponent::Terminal(
                            TerminalResolvedPathComponent::FnCall(resultant_term),
                        ))
                    }
                }
            }
        }
    }

    /// Resolve a path in the current context, returning a
    /// [`ResolvedAstPathComponent`] if successful.
    pub fn resolve_ast_path(&self, path: &AstPath) -> SemanticResult<ResolvedAstPathComponent> {
        debug_assert!(!path.is_empty());

        let mut resolved_path = self.resolve_ast_path_component(&path[0], None)?;

        for (index, component) in path.iter().enumerate().skip(1) {
            // For each component, we need to resolve it, and then namespace
            // further if possible.
            match resolved_path {
                ResolvedAstPathComponent::NonTerminal(non_terminal) => match non_terminal {
                    NonTerminalResolvedPathComponent::Data(data_def_id, args) => {
                        // Namespace further if it is a data member.
                        resolved_path = self.resolve_ast_path_component(
                            component,
                            Some((
                                NonTerminalResolvedPathComponent::Data(data_def_id, args),
                                component.span(),
                            )),
                        )?;
                    }
                    NonTerminalResolvedPathComponent::Mod(mod_def_id) => {
                        // Namespace further if it is a mod member.
                        resolved_path = self.resolve_ast_path_component(
                            component,
                            Some((
                                NonTerminalResolvedPathComponent::Mod(mod_def_id),
                                component.span(),
                            )),
                        )?;
                    }
                },
                ResolvedAstPathComponent::Terminal(_) => {
                    // Cannot namespace further
                    return Err(SemanticError::InvalidNamespaceSubject {
                        location: path[..index]
                            .iter()
                            .map(|c| c.span())
                            .reduce(|a, b| a.join(b))
                            .unwrap(),
                    });
                }
            };
        }

        Ok(resolved_path)
    }
}
