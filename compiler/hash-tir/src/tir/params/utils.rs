//! Utilities for working with parameters and arguments.
use std::collections::HashSet;

use hash_reporting::{
    diagnostic::{ErrorState, IntoCompound},
    hash_error_codes::error_codes::HashErrorCode,
    reporter::Reporter,
};
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_utils::{pluralise, printing::SequenceDisplay};

use crate::tir::{
    Arg, ArgId, ArgsId, HasAstNodeId, Node, NodeId, NodesId, ParamId, ParamIndex, ParamsId,
    PatArgId, PatArgsId,
};

/// An error that can occur when checking [Param]s against [Args].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamError {
    /// When there are too many arguments.
    TooManyArgs { expected: ParamsId, got: ArgsId },

    /// When an argument is specified more than once.
    DuplicateArg { first: ArgId, second: ArgId },

    /// When a parameter is specified more than once.
    DuplicateParam { first: ParamId, second: ParamId },

    /// When a positional argument is specified after an initial
    /// named argument, which makes it ambiguous which parameter the
    /// positional argument is referring to.
    PositionalArgAfterNamedArg { first_named: ArgId, next_positional: ArgId },

    /// When a default parameter is found before a required parameter.
    RequiredParamAfterDefaultParam { first_default: ParamId, next_required: ParamId },

    /// When an argument is named but no parameter with that name exists.
    ArgNameNotFoundInParams { arg: ArgId, params: ParamsId },

    /// Two parameters have differing names at the same index.
    ParamNameMismatch { param_a: ParamId, param_b: ParamId },

    /// When a required parameter is not found in the arguments.
    RequiredParamNotFoundInArgs { param: ParamId, args: ArgsId },

    /// When a spread is specified before a positional argument, which makes
    /// it impossible to determine which positional argument the spread should
    /// apply to.
    SpreadBeforePositionalArg { next_positional: ArgId },

    /// A collection of errors that occurred in a compound argument.
    Compound { errors: Vec<ParamError> },
}

impl ParamError {
    /// Adds the given [ParamError] to the [Reporter].
    pub fn add_to_reporter(&self, reporter: &mut Reporter) {
        match self {
            ParamError::Compound { errors } => {
                for error in errors {
                    error.add_to_reporter(reporter);
                }
            }
            ParamError::TooManyArgs { expected, got } => {
                let error =
                    reporter.error().code(HashErrorCode::ParameterLengthMismatch).title(format!(
                        "received {} argument{}, but expected at most {} argument{}",
                        got.len(),
                        pluralise!(got.len()),
                        expected.len(),
                        pluralise!(expected.len())
                    ));
                if let Some(location) = expected.span() {
                    error.add_labelled_span(
                        location,
                        format!(
                            "this definition expects at most {} argument{}",
                            expected.len(),
                            pluralise!(expected.len())
                        ),
                    );
                }
                if let Some(location) = {
                    let target = *got;
                    target.span()
                } {
                    error.add_labelled_span(
                        location,
                        format!("received {} argument{} here", got.len(), pluralise!(got.len())),
                    );
                }
            }
            ParamError::DuplicateArg { first, second } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ParameterInUse)
                    .title("received a duplicate argument");
                if let Some(location) = first.span() {
                    error.add_labelled_span(location, "first occurrence of this argument");
                }
                if let Some(location) = second.span() {
                    error.add_labelled_span(location, "second occurrence of this argument");
                }
            }
            ParamError::DuplicateParam { first, second } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ParameterInUse)
                    .title("received a duplicate parameter");
                if let Some(location) = first.span() {
                    error.add_labelled_span(location, "first occurrence of this parameter");
                }
                if let Some(location) = second.span() {
                    error.add_labelled_span(location, "second occurrence of this parameter");
                }
            }
            ParamError::PositionalArgAfterNamedArg { first_named, next_positional } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ParameterInUse)
                    .title("received a positional argument after a named argument");
                if let Some(location) = first_named.span() {
                    error.add_labelled_span(location, "first named argument");
                }
                if let Some(location) = next_positional.span() {
                    error.add_labelled_span(location, "next positional argument");
                }
                error.add_info("positional arguments must come before named arguments");
            }
            ParamError::RequiredParamAfterDefaultParam {
                first_default,
                next_required: next_non_default,
            } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ParameterInUse)
                    .title("found a required parameter after a default parameter");
                if let Some(location) = first_default.span() {
                    error.add_labelled_span(location, "first default parameter");
                }
                if let Some(location) = next_non_default.span() {
                    error.add_labelled_span(location, "next required parameter");
                }
                error.add_info("parameters with defaults must come after required parameters");
            }
            ParamError::ArgNameNotFoundInParams { arg, params } => {
                let error = reporter.error().code(HashErrorCode::ParameterInUse).title(format!(
                    "received an argument named `{}` but no parameter with that name exists",
                    arg
                ));
                if let Some(location) = arg.span() {
                    error.add_labelled_span(location, "argument with this name");
                }
                if let Some(location) = params.span() {
                    error.add_labelled_span(
                        location,
                        format!(
                            "expected one of these parameters: {}",
                            SequenceDisplay::either(
                                &params
                                    .iter()
                                    .map(|param| format!("{}", param.as_param_index()))
                                    .collect::<Vec<_>>()
                            )
                        ),
                    );
                }
            }
            ParamError::RequiredParamNotFoundInArgs { param, args } => {
                let error = reporter.error().code(HashErrorCode::ParameterInUse).title(format!(
                    "expected an argument named `{}` but none was found",
                    param.as_param_index()
                ));
                if let Some(location) = param.span() {
                    error.add_labelled_span(location, "parameter with this name");
                }
                if let Some(location) = {
                    let target = *args;
                    target.span()
                } {
                    error.add_labelled_span(
                        location,
                        format!(
                            "received {} argument{}: {}",
                            pluralise!("this", args.len()),
                            pluralise!(args.len()),
                            SequenceDisplay::either(
                                &args.iter().map(|arg| format!("{}", arg)).collect::<Vec<_>>()
                            )
                        ),
                    );
                }
            }
            ParamError::SpreadBeforePositionalArg { next_positional } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ParameterInUse)
                    .title("received a positional argument after a spread argument");
                if let Some(location) = next_positional.span() {
                    error.add_labelled_span(location, "next positional argument");
                }
                error.add_info("positional arguments must come before spread arguments");
            }
            ParamError::ParamNameMismatch { param_a, param_b } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::ParameterInUse)
                    .title("received two parameters with different names");
                if let Some(location) = param_a.span() {
                    error.add_labelled_span(location, "first parameter with this name");
                }
                if let Some(location) = param_b.span() {
                    error.add_labelled_span(location, "second parameter with this name");
                }
            }
        }
    }
}

impl IntoCompound for ParamError {
    fn into_compound(errors: Vec<ParamError>) -> ParamError {
        ParamError::Compound { errors }
    }
}

pub type ParamResult<T> = Result<T, ParamError>;

/// Validate the given parameters, returning an error if they are invalid.
///
/// Conditions for valid parameters are:
/// 1. No duplicate parameter names
/// 2. All parameters with defaults are at the end
pub fn validate_params(params_id: ParamsId) -> ParamResult<()> {
    let mut error_state = ErrorState::new();

    let mut seen = HashSet::new();
    let mut found_default = None;

    for param in params_id.iter() {
        // Check for duplicate parameters
        if let Some(param_name) = param.borrow().name_ident() {
            if seen.contains(&param_name) {
                error_state.add_error(ParamError::DuplicateParam { first: param, second: param });
            }
            seen.insert(param_name);
        }

        // Ensure that parameters with defaults follow parameters without
        // defaults
        if let Some(default_param) = found_default {
            if param.borrow().default.is_none() {
                // Required parameter after named parameter,
                // error
                error_state.add_error(ParamError::RequiredParamAfterDefaultParam {
                    first_default: default_param,
                    next_required: param,
                });
            }
        } else if param.borrow().default.is_some() {
            // Found the first default parameter
            found_default = Some(param);
        }
    }

    error_state.into_error(|| Ok(()))
}

/// Validate the given arguments against the given parameters, returning an
/// error if they are invalid.
///
/// Conditions for valid arguments are:
/// 1. No duplicate argument names
/// 2. All named arguments follow positional arguments
/// 3. No more arguments than parameters
///
/// The specific unification of the argument and parameter types is not
/// checked at this stage. The function
/// `validate_and_reorder_args_against_params` performs additional
/// validation of the argument names, reorders the arguments to match
/// the parameters, and fills in default arguments.
pub fn validate_args_against_params(args_id: ArgsId, params_id: ParamsId) -> ParamResult<()> {
    let mut error_state = ErrorState::new();

    // Check for too many arguments
    if args_id.len() > params_id.len() {
        error_state.add_error(ParamError::TooManyArgs { expected: params_id, got: args_id });
    }

    let mut seen = HashSet::new();
    let mut found_named = None;

    for arg in args_id.iter() {
        let target = arg.value().data.target;

        // Check for duplicate arguments
        match target {
            ParamIndex::Name(arg_name) => {
                if seen.contains(&arg_name) {
                    error_state.add_error(ParamError::DuplicateArg { first: arg, second: arg });
                }
                seen.insert(arg_name);
            }
            ParamIndex::Position(_) => {
                // no-op, we assume that there are no duplicate positional
                // arguments..
            }
        }

        // Ensure that named arguments follow positional arguments
        match found_named {
            Some(named_arg) => {
                match target {
                    ParamIndex::Name(_) => {
                        // Named arguments, ok
                    }
                    ParamIndex::Position(_) => {
                        // Positional arguments after named arguments, error
                        error_state.add_error(ParamError::PositionalArgAfterNamedArg {
                            first_named: named_arg,
                            next_positional: arg,
                        });
                    }
                }
            }
            None => match target {
                ParamIndex::Name(_) => {
                    // Found the first named argument
                    found_named = Some(arg);
                }
                ParamIndex::Position(_) => {
                    // Still positional arguments, ok
                }
            },
        }
    }

    error_state.into_error(|| Ok(()))
}

/// Validate the given arguments against the given parameters and
/// reorder the arguments to match the parameters. Additionally, add
/// wildcard members to the pattern arguments where appropriate if
/// there is a spread.
///
/// This does not modify the arguments or parameters, but instead returns a
/// new argument list.
///
/// *Invariant*: The parameters have already been validated through
/// `validate_params`.
///
/// *Invariant*: The input arguments are *not* already validated/reordered.
pub fn validate_and_reorder_args_against_params(
    args_id: PatArgsId,
    params_id: ParamsId,
) -> ParamResult<PatArgsId> {
    // First validate the arguments
    validate_args_against_params(args_id, params_id)?;

    let spread = args_id.get_spread();

    let mut error_state = ErrorState::new();
    let mut result: Vec<Option<Node<Arg>>> = vec![None; params_id.len()];

    // Note: We have already validated that the number of arguments is less than
    // or equal to the number of parameters

    for (j, arg_id) in args_id.iter().enumerate() {
        let arg = arg_id.value();

        match arg.target {
            // Invariant: all positional arguments are before named
            ParamIndex::Position(j_received) => {
                assert!(j_received as usize == j);

                // If the previous argument was a spread, this is an error
                if let Some(spread) = spread
                    && j != 0
                    && spread.index == j - 1
                {
                    error_state.add_error(ParamError::SpreadBeforePositionalArg {
                        next_positional: arg_id,
                    });
                }

                result[j] = Some(Node::at(
                    Arg {
                        // Add the name if present
                        target: (ParamId::new(params_id.elements(), j)).as_param_index(),
                        value: arg.value,
                    },
                    arg.origin,
                ));
            }
            ParamIndex::Name(arg_name) => {
                // Find the position in the parameter list of the parameter with the
                // same name as the argument
                let maybe_param_index =
                    params_id.iter().position(|param_id| match (param_id).borrow().name_ident() {
                        Some(name) => name == arg_name,
                        None => false,
                    });

                match maybe_param_index {
                    Some(i) => {
                        if result[i].is_some() {
                            // Duplicate argument name, must be from positional
                            assert!(j != i);
                            error_state.add_error(ParamError::DuplicateArg {
                                first: PatArgId::new(args_id.elements(), i),
                                second: PatArgId::new(args_id.elements(), j),
                            });
                        } else {
                            // Found an uncrossed parameter, add it to the result
                            result[i] = Some(Node::at(
                                Arg { target: arg.target, value: arg.value },
                                arg.origin,
                            ));
                        }
                    }
                    None => {
                        // No parameter with the same name as the argument
                        error_state.add_error(ParamError::ArgNameNotFoundInParams {
                            arg: arg_id,
                            params: params_id,
                        });
                    }
                }
            }
        }
    }

    // If there were any errors, return them
    if error_state.has_errors() {
        return error_state.into_error(|| unreachable!());
    }

    // Populate missing arguments with wildcards
    for i in params_id.to_index_range() {
        if result[i].is_none() {
            let param_id = ParamId::new(params_id.elements(), i);
            let param = param_id.borrow();
            let default = param.default;

            if let Some(default) = default {
                // If there is a default value, add it to the result
                result[i] = Some(Node::at(
                    Arg { target: param_id.as_param_index(), value: default },
                    param.origin,
                ));
            } else {
                // No default value, and not present in the arguments, so
                // this is an error
                error_state.add_error(ParamError::RequiredParamNotFoundInArgs {
                    param: param_id,
                    args: args_id,
                });
            }
        }
    }

    // If there were any errors, return them
    if error_state.has_errors() {
        return error_state.into_error(|| unreachable!());
    }

    // Now, create the new argument list
    // There should be no `None` elements at this point
    let new_args_id = Node::create_at(
        Node::<Arg>::seq(result.into_iter().map(|arg| arg.unwrap())),
        args_id.origin(),
    );

    Ok(new_args_id)
}
