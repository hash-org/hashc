//! This module contains functionality to resolve item paths in the AST.
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
use hash_types::new::{
    args::{ArgData, ArgsId},
    data::{CtorPat, CtorTerm, DataDefId},
    defs::{DefArgGroupData, DefArgsId, DefParamsId},
    environment::{
        context::{Binding, BindingKind, ScopeKind},
        env::AccessToEnv,
    },
    fns::{FnCallTerm, FnDefId},
    mods::{ModDefId, ModMemberValue},
    params::ParamTarget,
    scopes::BoundVar,
    terms::{Term, TermId},
};
use hash_utils::store::{SequenceStore, SequenceStoreKey, Store};

use super::{ContextKind, SymbolResolutionPass};
use crate::new::{
    diagnostics::{
        error::{TcError, TcResult},
        params::{SomeArgsId, SomeDefArgsId},
    },
    environment::tc_env::WithTcEnv,
    ops::{common::CommonOps, AccessToOps},
    passes::ast_pass::AstPass,
};
/// An argument group in the AST.
///
/// This is either a group of explicit `(a, b, c)` arguments, or a group of
/// implicit `<a, b, c>` arguments. The former corresponds to the
/// [`ast::ConstructorCallArg`], while the latter corresponds to the
/// [`ast::TyArg`].
#[derive(Copy, Clone, Debug)]
pub enum AstArgGroup<'a> {
    /// A group of explicit `(a, b, c)` arguments.
    ExplicitArgs(&'a ast::AstNodes<ast::ConstructorCallArg>),
    /// A group of implicit `<a, b, c>` arguments.
    ImplicitArgs(&'a ast::AstNodes<ast::TyArg>),
    /// A group of explicit `(p, q, r)` pattern arguments
    ExplicitPatArgs(
        &'a ast::AstNodes<ast::TuplePatEntry>,
        &'a Option<ast::AstNode<ast::SpreadPat>>,
    ),
    // @@Todo: implicit pattern arguments when AST supports this
}

impl AstArgGroup<'_> {
    /// Get the span of this argument group.
    pub fn span(&self) -> Option<Span> {
        match self {
            AstArgGroup::ExplicitArgs(args) => args.span(),
            AstArgGroup::ImplicitArgs(args) => args.span(),
            AstArgGroup::ExplicitPatArgs(args, _) => args.span(),
        }
    }
}

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
            span.join(last_arg.span().unwrap())
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
    Data(DataDefId, DefArgsId),
    /// A module definition with some arguments.
    Mod(ModDefId, DefArgsId),
}

/// Each non-terminal resolved path component is a module member.
impl From<NonTerminalResolvedPathComponent> for ModMemberValue {
    fn from(value: NonTerminalResolvedPathComponent) -> Self {
        match value {
            NonTerminalResolvedPathComponent::Data(data_def_id, _) => {
                ModMemberValue::Data(data_def_id)
            }
            NonTerminalResolvedPathComponent::Mod(mod_def_id, _) => ModMemberValue::Mod(mod_def_id),
        }
    }
}

impl fmt::Display for WithTcEnv<'_, &NonTerminalResolvedPathComponent> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let env = self.tc_env().env();
        write!(f, "{}", env.with(env.with(ModMemberValue::from(*self.value)).name()))
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
    BoundVar(BoundVar),
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
impl<'tc> SymbolResolutionPass<'tc> {
    /// Resolve a name starting from the given [`ModMemberValue`], or the
    /// current context if no such value is given.
    ///
    /// Returns the binding that the name resolves to.
    pub fn resolve_ast_name(
        &self,
        name: Identifier,
        name_span: Span,
        starting_from: Option<(NonTerminalResolvedPathComponent, Span)>,
    ) -> TcResult<Binding> {
        match starting_from {
            Some((member_value, _span)) => match member_value {
                // If we are starting from a module or data type, we need to enter their scopes.
                NonTerminalResolvedPathComponent::Data(data_def_id, _) => self.enter_scope(
                    ScopeKind::Data(data_def_id),
                    ContextKind::Access(member_value, data_def_id.into()),
                    || self.resolve_ast_name(name, name_span, None),
                ),
                NonTerminalResolvedPathComponent::Mod(mod_def_id, _) => self.enter_scope(
                    ScopeKind::Mod(mod_def_id),
                    ContextKind::Access(member_value, mod_def_id.into()),
                    || self.resolve_ast_name(name, name_span, None),
                ),
            },
            None => {
                // If there is no start point, try to lookup the variable in the current scope.
                let binding_symbol = self.lookup_binding_by_name_or_error(
                    name,
                    name_span,
                    self.get_current_context_kind(),
                )?;
                Ok(self.context().get_binding(binding_symbol).unwrap())
            }
        }
    }

    /// Make [`ArgsId`] from an AST argument group, with holes for all the
    /// arguments.
    pub fn make_args_from_ast_arg_group(&self, group: &AstArgGroup) -> ArgsId {
        macro_rules! make_args_from_ast_args {
            ($args:expr) => {
                self.param_ops().create_args($args.iter().enumerate().map(|(i, arg)| {
                    return ArgData {
                        target: arg
                            .name
                            .as_ref()
                            .map(|name| ParamTarget::Name(name.ident))
                            .unwrap_or_else(|| ParamTarget::Position(i)),
                        value: self.new_term_hole(),
                    };
                }))
            };
        }
        match group {
            AstArgGroup::ExplicitArgs(args) => make_args_from_ast_args!(args),
            AstArgGroup::ImplicitArgs(args) => make_args_from_ast_args!(args),
            AstArgGroup::ExplicitPatArgs(_, _) => {
                todo!()
            }
        }
    }

    /// Make [`DefArgsId`] from a list of AST argument groups, using
    /// `make_args_from_ast_arg_group` to make each argument group.
    fn make_def_args_from_ast_arg_groups(
        &self,
        groups: &[AstArgGroup],
        originating_params: DefParamsId,
    ) -> DefArgsId {
        self.param_ops().create_def_args(groups.iter().enumerate().map(|(index, group)| {
            DefArgGroupData {
                args: self.make_args_from_ast_arg_group(group),
                param_group: (originating_params, index),
            }
        }))
    }

    /// Wrap a term in a function call, given a list of arguments as a list of
    /// [`AstArgGroup`].
    ///
    /// Creates a new [`TermId`], which is a term that represents the
    /// function call, and might be nested depending on `args`.
    fn wrap_term_in_fn_call_from_ast_args(
        &self,
        subject: TermId,
        args: &[AstArgGroup],
    ) -> FnCallTerm {
        debug_assert!(!args.is_empty());
        let mut current_subject = subject;
        for arg_group in args {
            let args = self.make_args_from_ast_arg_group(arg_group);
            current_subject = self.new_term(Term::FnCall(FnCallTerm {
                subject: current_subject,
                args,
                implicit: matches!(arg_group, AstArgGroup::ImplicitArgs(_)),
            }));
        }
        match self.get_term(current_subject) {
            Term::FnCall(call) => call,
            _ => unreachable!(),
        }
    }

    /// Apply the given list of AST arguments to the given definition
    /// parameters, checking that the lengths match in the process.
    ///
    /// If successful, returns the [`DefArgsId`] that represents the arguments.
    ///
    /// Otherwise, returns an error.
    fn apply_ast_args_to_def_params(
        &self,
        def_params: DefParamsId,
        args: &[AstArgGroup],
    ) -> TcResult<DefArgsId> {
        // @@Todo: implicit args
        // @@Todo: default params

        // First ensure that the number of parameter and argument groups match.
        let created_def_args = self.make_def_args_from_ast_arg_groups(args, def_params);
        if def_params.len() != created_def_args.len() {
            return Err(TcError::WrongDefArgLength {
                def_params_id: def_params,
                def_args_id: SomeDefArgsId::Args(created_def_args),
            });
        }

        // Then ensure that the number of parameters and arguments in each group
        // match.
        let mut errors: Vec<TcError> = vec![];
        for (param_group_index, arg_group_index) in
            def_params.to_index_range().zip(created_def_args.to_index_range())
        {
            let def_param_group =
                self.stores().def_params().get_element((def_params, param_group_index));
            let def_arg_group =
                self.stores().def_args().get_element((created_def_args, arg_group_index));

            if def_param_group.params.len() != def_arg_group.args.len() {
                // Collect errors and only report at the end.
                errors.push(TcError::WrongArgLength {
                    params_id: def_param_group.params,
                    args_id: SomeArgsId::Args(def_arg_group.args),
                });
            }
        }
        if !errors.is_empty() {
            return Err(TcError::Compound { errors });
        }

        Ok(created_def_args)
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
    ) -> TcResult<ResolvedAstPathComponent> {
        let binding = self.resolve_ast_name(component.name, component.name_span, starting_from)?;

        match binding.kind {
            BindingKind::ModMember(_, mod_member_id) => {
                let mod_member = self.stores().mod_members().get_element(mod_member_id);
                match mod_member.value {
                    ModMemberValue::Data(data_def_id) => {
                        let data_def_params =
                            self.stores().data_def().map_fast(data_def_id, |def| def.params);
                        let args =
                            self.apply_ast_args_to_def_params(data_def_params, &component.args)?;
                        Ok(ResolvedAstPathComponent::NonTerminal(
                            NonTerminalResolvedPathComponent::Data(data_def_id, args),
                        ))
                    }
                    ModMemberValue::Mod(mod_def_id) => {
                        let mod_def_params =
                            self.stores().mod_def().map_fast(mod_def_id, |def| def.params);
                        let args =
                            self.apply_ast_args_to_def_params(mod_def_params, &component.args)?;
                        Ok(ResolvedAstPathComponent::NonTerminal(
                            NonTerminalResolvedPathComponent::Mod(mod_def_id, args),
                        ))
                    }
                    ModMemberValue::Fn(fn_def_id) => match &component.args[..] {
                        [] => Ok(ResolvedAstPathComponent::Terminal(
                            TerminalResolvedPathComponent::FnDef(fn_def_id),
                        )),
                        args => {
                            let resultant_term = self.wrap_term_in_fn_call_from_ast_args(
                                self.new_term(Term::FnRef(fn_def_id)),
                                args,
                            );
                            Ok(ResolvedAstPathComponent::Terminal(
                                TerminalResolvedPathComponent::FnCall(resultant_term),
                            ))
                        }
                    },
                }
            }
            BindingKind::Ctor(_, ctor_def_id) => {
                // A constructor cannot be namespaced further.
                match component.args[0] {
                    AstArgGroup::ExplicitPatArgs(_, _) => {
                        todo!()
                    }
                    AstArgGroup::ExplicitArgs(_) | AstArgGroup::ImplicitArgs(_) => {
                        let ctor_def = self.stores().ctor_defs().get_element(ctor_def_id);

                        // Apply the arguments to the constructor.
                        let args =
                            self.apply_ast_args_to_def_params(ctor_def.params, &component.args)?;
                        Ok(ResolvedAstPathComponent::Terminal(
                            TerminalResolvedPathComponent::CtorTerm(CtorTerm {
                                ctor: ctor_def_id,
                                args,
                            }),
                        ))
                    }
                }
            }
            BindingKind::BoundVar(bound_var) => {
                // If the subject has no args, it is a bound variable, otherwise it is a
                // function call.
                match &component.args[..] {
                    [] => Ok(ResolvedAstPathComponent::Terminal(
                        TerminalResolvedPathComponent::BoundVar(BoundVar {
                            name: binding.name,
                            origin: bound_var,
                        }),
                    )),
                    args => {
                        let resultant_term = self.wrap_term_in_fn_call_from_ast_args(
                            self.new_term(Term::Var(BoundVar {
                                name: binding.name,
                                origin: bound_var,
                            })),
                            args,
                        );
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
    pub fn resolve_ast_path(&self, path: &AstPath) -> TcResult<ResolvedAstPathComponent> {
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
                    NonTerminalResolvedPathComponent::Mod(mod_def_id, args) => {
                        // Namespace further if it is a mod member.
                        resolved_path = self.resolve_ast_path_component(
                            component,
                            Some((
                                NonTerminalResolvedPathComponent::Mod(mod_def_id, args),
                                component.span(),
                            )),
                        )?;
                    }
                },
                ResolvedAstPathComponent::Terminal(_) => {
                    // Cannot namespace further
                    return Err(TcError::InvalidNamespaceSubject {
                        location: self.source_location(
                            path[..index]
                                .iter()
                                .map(|c| c.span())
                                .reduce(|a, b| a.join(b))
                                .unwrap(),
                        ),
                    });
                }
            };
        }

        Ok(resolved_path)
    }
}
