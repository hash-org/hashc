//! Operations related to handling parameters.

use std::{borrow::Cow, collections::HashSet};

use hash_ast::ast::ParamOrigin;
use hash_source::{identifier::Identifier, location::SourceLocation};
use hash_types::{
    arguments::ArgsId,
    location::LocationTarget,
    params::{GetNameOpt, Param, ParamList, Params, ParamsId},
};
use itertools::Itertools;

use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        params::ParamListKind,
    },
    storage::{AccessToStorage, StorageRef},
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

    let args_kind = ParamListKind::Args(args_id);

    if params.len() < args.len() {
        return Err(TcError::MismatchingArgParamLength {
            args_kind,
            params_id,
            params_location: params_subject.into(),
            args_location: args_subject.into(),
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
                            return Err(TcError::ParamGivenTwice { param_kind: args_kind, index });
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
                            args_kind,
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
                        param_kind: args_kind,
                        index: i,
                    });
                } else if used_params.contains(&i) {
                    // Ensure not already used
                    return Err(TcError::ParamGivenTwice { param_kind: args_kind, index: i });
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
            args_kind: ParamListKind::Args(args_id),
            params_id,
            params_location: params_subject.into(),
            args_location: args_subject.into(),
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
pub(crate) fn validate_param_list<T: Clone + GetNameOpt>(
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

/// Function that validates a parameter list without considering the ordering of
/// named and un-named parameters. This is a useful function for constructor
/// pattern fields since there is no bound on which order the user specifies
/// names on the fields. This function will simply verify that the fields
/// don't repeat names.
pub(crate) fn validate_param_list_unordered<T: Clone + GetNameOpt>(
    params: &ParamList<T>,
    origin: ParamListKind,
) -> TcResult<()> {
    // Keep track of used params to ensure no parameter is given twice.
    let mut params_used = HashSet::new();

    for (index, param) in params.positional().iter().enumerate() {
        // If we have found the index in our set, that means that it must
        // of already been used and therefore it should trigger an error
        if let Some(name) = param.get_name_opt() {
            if let Some((found_index, _)) = params.get_by_name(name) {
                if params_used.contains(&found_index) {
                    return Err(TcError::ParamGivenTwice { param_kind: origin, index });
                } else {
                    params_used.insert(found_index);
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
    args_id: ParamListKind,
    subject: impl Into<LocationTarget>,
) -> TcResult<()> {
    for arg in args.positional() {
        if let Some(name) = arg.get_name_opt() {
            if params.get_by_name(name).is_none() {
                return Err(TcError::ParamNotFound {
                    args_kind: args_id,
                    params_subject: subject.into(),
                    name,
                });
            }
        }
    }

    Ok(())
}

pub struct ParamOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for ParamOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> ParamOps<'tc> {
    /// Create a new instance of [ParamOps]
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Convert a [ParamListKind] and a field index into a [SourceLocation] by
    /// looking up the inner id within the
    /// [LocationStore][hash_types::location::LocationStore].
    pub(crate) fn field_location(
        &self,
        param: &ParamListKind,
        index: usize,
    ) -> Option<SourceLocation> {
        match param {
            ParamListKind::Params(id) => self.location_store().get_location((*id, index)),
            ParamListKind::PatArgs(id) => self.location_store().get_location((*id, index)),
            ParamListKind::Args(id) => self.location_store().get_location((*id, index)),
        }
    }

    /// Get the [ParamOrigin] from the [ParamListKind]
    pub(crate) fn origin(&self, param: &ParamListKind) -> ParamOrigin {
        match param {
            ParamListKind::Params(id) => self.params_store().get_origin(*id),
            ParamListKind::PatArgs(id) => self.pat_args_store().get_origin(*id),
            ParamListKind::Args(id) => self.args_store().get_origin(*id),
        }
    }

    /// Get the names fields within the [ParamListKind]
    pub(crate) fn names(&self, param: &ParamListKind) -> HashSet<Identifier> {
        match param {
            ParamListKind::Params(id) => self.params_store().names(*id),
            ParamListKind::PatArgs(id) => self.pat_args_store().names(*id),
            ParamListKind::Args(id) => self.args_store().names(*id),
        }
    }

    /// Get a stored parameter/field by name.
    pub(crate) fn get_name_by_index(
        &self,
        param: &ParamListKind,
        name: Identifier,
    ) -> Option<usize> {
        match param {
            ParamListKind::Params(id) => {
                self.params_store().get_by_name(*id, name).map(|param| param.0)
            }
            ParamListKind::PatArgs(id) => {
                self.pat_args_store().get_by_name(*id, name).map(|param| param.0)
            }
            ParamListKind::Args(id) => {
                self.args_store().get_by_name(*id, name).map(|param| param.0)
            }
        }
    }

    /// Function used to compute the missing fields from another
    /// [ParamListKind]. This does not compute a difference as it doesn't
    /// consider items that are present in the other [ParamListKind] and not
    /// in the current list as `missing`.
    pub(crate) fn compute_missing_fields(
        &self,
        param: &ParamListKind,
        other: &ParamListKind,
    ) -> Vec<Identifier> {
        let lhs_names = self.names(param);
        let rhs_names = self.names(other);

        // Compute the missing names and then sort them
        let mut missing_names = lhs_names.difference(&rhs_names).into_iter().copied().collect_vec();
        missing_names.sort_unstable();

        missing_names
    }
}
