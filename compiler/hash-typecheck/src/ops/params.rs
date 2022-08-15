//! Operations related to handling parameters.

use std::{borrow::Cow, collections::HashSet};

use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        params::ParamListKind,
    },
    storage::{
        arguments::ArgsId,
        location::LocationTarget,
        params::ParamsId,
        primitives::{GetNameOpt, Param, ParamList, Params},
    },
};

/// Pair the given parameters with the given parameter list (either args, or
/// pattern params).
///
/// This does not perform any typechecking, it simply matches parameters by
/// position or name.
///
/// The `infer_arg_from_default_param` closure is used to create a `T` arg type
/// from a parameter that has a default value but was not provided in the
/// argument list.
pub(crate) fn pair_args_with_params<'p, 'a, T: Clone + GetNameOpt>(
    params: &'p Params<'_>,
    args: &'a ParamList<'_, T>,
    params_id: ParamsId,
    args_id: ArgsId,
    mut infer_arg_from_default_param: impl FnMut(&Param) -> T,
    params_subject: impl Into<LocationTarget>,
    args_subject: impl Into<LocationTarget>,
) -> TcResult<Vec<(&'p Param, Cow<'a, T>)>> {
    let mut result = vec![];

    // Keep track of used params to ensure no parameter is given twice.
    let mut used_params = HashSet::new();

    // We want to count the number of default arguments, it should be
    // impossible to have a `default` value for a parameter and it be
    // un-named...
    let mut default_params: HashSet<_> = params
        .positional()
        .iter()
        .filter(|param| param.default_value.is_some() && param.name.is_some())
        .map(|param| param.name.unwrap())
        .collect();

    let origin = ParamListKind::Args(args_id);

    if params.len() < args.len() {
        return Err(TcError::MismatchingArgParamLength {
            args_id,
            params_id,
            params_subject: params_subject.into(),
            args_subject: args_subject.into(),
        });
    }

    // Keep track of the first non-positional argument
    let mut done_positional = false;

    // Iterate over the arguments and check that they are in the correct order
    for (i, arg) in args.positional().iter().enumerate() {
        match arg.get_name_opt() {
            // Named argument
            Some(arg_name) => {
                done_positional = true;

                match params.get_by_name(arg_name) {
                    Some((index, param)) => {
                        if used_params.contains(&index) {
                            // Ensure not already used
                            return Err(TcError::ParamGivenTwice { param_kind: origin, index });
                        } else {
                            used_params.insert(index);
                            result.push((param, Cow::Borrowed(arg)));

                            // If the parameter has a `default` value, we need to remove it from the
                            // `default_params` list because it is being overridden by the call site
                            // specifying a value for it
                            default_params.remove(&arg_name);
                        }
                    }
                    None => {
                        // We want to show the location of the argument that doesn't exist, the name
                        // of the argument and where the initial parameter
                        // constructor is defined...
                        return Err(TcError::ParamNotFound {
                            params_subject: params_subject.into(),
                            args_kind: origin,
                            params_id,
                            name: arg_name,
                        });
                    }
                }
            }
            // Positional argument
            None => {
                if done_positional {
                    // Using positional args after named args is an error
                    return Err(TcError::AmbiguousArgumentOrdering {
                        param_kind: origin,
                        index: i,
                    });
                } else if used_params.contains(&i) {
                    // Ensure not already used
                    return Err(TcError::ParamGivenTwice { param_kind: origin, index: i });
                } else {
                    used_params.insert(i);

                    let param = params.positional().get(i).unwrap();
                    result.push((param, Cow::Borrowed(arg)));

                    // If the parameter has a `default` value, we need to remove
                    // it from the `default_params` list
                    if let Some(name) = param.name {
                        default_params.remove(&name);
                    }
                }
            }
        }
    }

    // For any default parameters that are left, we need to insert the into the
    // result by applying the inference function which converts a parameter into the
    // given argument `T`
    for default_param in &default_params {
        let (_, param) = params.get_by_name(*default_param).unwrap();

        result.push((param, Cow::Owned(infer_arg_from_default_param(param))));
    }

    // Compare the parameter list subtracted from the `default_params` that weren't
    // specified by the arguments. The size of both results should now be the
    // same, or there are arguments missing...
    if params.positional().len() != result.len() {
        // @@Todo: for pattern params, use a more specialised error here
        return Err(TcError::MismatchingArgParamLength {
            args_id,
            params_id,
            params_subject: params_subject.into(),
            args_subject: args_subject.into(),
        });
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
/// parameters or arguments, and hence why it accepts a [ParamListKind]
/// in order to preserve context in the event of an error.
pub(crate) fn validate_param_list_ordering<T: Clone + GetNameOpt>(
    params: &ParamList<T>,
    origin: ParamListKind,
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
                        return Err(TcError::ParamGivenTwice { param_kind: origin, index });
                    } else {
                        params_used.insert(found_index);
                    }
                }
            }
            None => {
                // Using positional args after named args is an error
                if done_positional {
                    return Err(TcError::AmbiguousArgumentOrdering { param_kind: origin, index });
                }
            }
        }
    }

    Ok(())
}

/// Function to validate that all of the named arguments specified in
/// `args` exist within the specified `params`.
pub(crate) fn validate_named_params_match<T: Clone + GetNameOpt>(
    params: &Params<'_>,
    args: &ParamList<'_, T>,
    params_id: ParamsId,
    args_id: ParamListKind,
    subject: impl Into<LocationTarget>,
) -> TcResult<()> {
    for arg in args.positional() {
        if let Some(name) = arg.get_name_opt() {
            if params.get_by_name(name).is_none() {
                return Err(TcError::ParamNotFound {
                    params_id,
                    args_kind: args_id,
                    params_subject: subject.into(),
                    name,
                });
            }
        }
    }

    Ok(())
}
