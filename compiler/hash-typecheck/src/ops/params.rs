//! Operations related to handling parameters.
use crate::{
    error::{TcError, TcResult},
    storage::primitives::{Arg, Args, Param, Params},
};
use std::collections::HashSet;

/// Pair the given parameters with the given arguments.
///
/// This does not perform any typechecking, it simply matches parameters and arguments by
/// position or name.
pub fn pair_args_with_params<'p, 'a>(
    params: &'p Params,
    args: &'a Args,
) -> TcResult<Vec<(&'p Param, &'a Arg)>> {
    let mut result = vec![];

    // Keep track of used params to ensure no parameter is given twice.
    let mut params_used = HashSet::new();

    // @@Incomplete: handle default args

    // Ensure the length of params and args is the same
    if params.positional().len() != args.positional().len() {
        return Err(TcError::MismatchingArgParamLength {
            args: args.clone(),
            params: params.clone(),
        });
    }

    // Keep track of the first non-positional argument
    let mut done_positional = false;
    for (i, arg) in args.positional().iter().enumerate() {
        match arg.name {
            Some(arg_name) => {
                // Named argument
                done_positional = true;
                match params.get_by_name(arg_name) {
                    Some((param_i, param)) => {
                        if params_used.contains(&i) {
                            // Ensure not already used
                            return Err(TcError::ParamGivenTwice {
                                args: args.clone(),
                                params: params.clone(),
                                param_index_given_twice: param_i,
                            });
                        } else {
                            params_used.insert(param_i);
                            result.push((param, arg));
                        }
                    }
                    None => {
                        return Err(TcError::ParamNotFound {
                            field1: params.clone(),
                            field2: arg_name,
                        })
                    }
                }
            }
            None => {
                // Positional argument
                if done_positional {
                    // Using positional args after named args is an error that should have been
                    // caught at semantic analysis.
                    panic!("Found positional arguments after named args, should have been caught during semantic analysis.")
                } else if params_used.contains(&i) {
                    // Ensure not already used
                    return Err(TcError::ParamGivenTwice {
                        args: args.clone(),
                        params: params.clone(),
                        param_index_given_twice: i,
                    });
                } else {
                    params_used.insert(i);
                    result.push((params.positional().get(i).unwrap(), arg));
                }
            }
        }
    }

    Ok(result)
}
