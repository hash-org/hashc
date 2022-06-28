//! Operations related to handling parameters.

use crate::{
    error::{ParameterListOrigin, TcError, TcResult},
    storage::primitives::{
        Arg, Args, ArgsId, GetNameOpt, Param, ParamList, Params, ParamsId, TermId,
    },
};
use std::collections::HashSet;

/// Pair the given parameters with the given arguments.
///
/// This does not perform any typechecking, it simply matches parameters and
/// arguments by position or name.
pub(crate) fn pair_args_with_params<'p, 'a>(
    params: &'p Params,
    args: &'a Args,
    parent: TermId,
    params_id: ParamsId,
    args_id: ArgsId,
) -> TcResult<Vec<(&'p Param, &'a Arg)>> {
    let mut result = vec![];

    // Keep track of used params to ensure no parameter is given twice.
    let mut params_used = HashSet::new();

    // @@Incomplete: handle default args

    // Ensure the length of params and args is the same
    if params.positional().len() != args.positional().len() {
        return Err(TcError::MismatchingArgParamLength {
            args: args_id,
            params: params_id,
            target: parent,
        });
    }

    let origin = ParameterListOrigin::Args(args_id);

    // Keep track of the first non-positional argument
    let mut done_positional = false;
    for (i, arg) in args.positional().iter().enumerate() {
        match arg.name {
            Some(arg_name) => {
                // Named argument
                done_positional = true;
                match params.get_by_name(arg_name) {
                    Some((param_i, param)) => {
                        if params_used.contains(&param_i) {
                            // Ensure not already used
                            return Err(TcError::ParamGivenTwice { origin, index: param_i });
                        } else {
                            params_used.insert(param_i);
                            result.push((param, arg));
                        }
                    }
                    None => {
                        return Err(TcError::ParamNotFound { params: params_id, name: arg_name })
                    }
                }
            }
            None => {
                // Positional argument
                if done_positional {
                    // Using positional args after named args is an error
                    return Err(TcError::CannotUsePositionalArgAfterNamedArg { origin, index: i });
                } else if params_used.contains(&i) {
                    // Ensure not already used
                    return Err(TcError::ParamGivenTwice { origin, index: i });
                } else {
                    params_used.insert(i);
                    result.push((params.positional().get(i).unwrap(), arg));
                }
            }
        }
    }

    Ok(result)
}

/// Verify that a [ParamList<T>] adheres to the standard rules of ordering for
/// named fields. The two rules that must hold within the parameter list are:
///
/// - Named parameters cannot be used more than once.
///
/// - Un-named parameters must not be used after named ones.
///
/// This does not perform any typechecking, it simply checks that the given
/// [ParamList] follows the described rules. This function works for either
/// parameters or arguments, and hence why it accepts a [ParameterListOrigin]
/// in order to preserve context in the event of an error.
pub(crate) fn validate_param_list_ordering<'p, T: Clone + GetNameOpt>(
    params: &'p ParamList<T>,
    origin: ParameterListOrigin,
) -> TcResult<()> {
    // Keep track of used params to ensure no parameter is given twice.
    let mut params_used = HashSet::new();

    // Keep track of when positional parameters are in use
    let mut done_positional = false;

    for (index, param) in params.positional().iter().enumerate() {
        // If the parameter has a name, verify that it is only being used once
        match param.get_name_opt() {
            Some(name) => {
                done_positional = true;

                // If we have found the index in our set, that means that it must
                // of already been used and therefore it should trigger an error
                if let Some((found_index, _)) = params.get_by_name(name) {
                    if params_used.contains(&found_index) {
                        return Err(TcError::ParamGivenTwice { origin, index });
                    } else {
                        params_used.insert(found_index);
                    }
                }
            }
            None => {
                // Using positional args after named args is an error
                if done_positional {
                    return Err(TcError::CannotUsePositionalArgAfterNamedArg { origin, index });
                }
            }
        }
    }

    Ok(())
}
