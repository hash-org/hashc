//! Functionality related to pattern matching.

use std::{
    cmp::min,
    collections::{HashMap, HashSet},
};

use hash_ast::ast::ParamOrigin;
use hash_reporting::diagnostic::Diagnostics;
use hash_source::identifier::Identifier;
use hash_types::{
    arguments::ArgOld,
    nominals::StructFields,
    params::{AccessOp, ParamsId},
    pats::{
        AccessPat, ConstPat, ConstructorPat, IfPat, ListPat, ModPat, Pat, PatArg, PatArgsId, PatId,
        SpreadPat,
    },
    scope::{Member, Mutability},
    terms::TermId,
};
use hash_utils::store::{CloneStore, Store};
use itertools::Itertools;

use super::{params::validate_named_params_match, AccessToOps};
use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::tc_panic,
        params::ParamListKind,
        warning::TcWarning,
    },
    ops::validate::TermValidation,
    storage::{AccessToStorage, StorageRef},
};

/// Contains functions related to pattern matching.
pub struct PatMatcher<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for PatMatcher<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

/// A pattern that occurs in a position within a declaration or some
/// other binding structure. The [PatMember] represents the relation
/// between the underlying [Pat] and the scope [Member].
#[derive(Debug, Clone)]
struct PatMember {
    /// The id of the pattern.
    pat: PatId,
    /// The member that the pattern is bound to.
    member: Member,
}

impl<'tc> PatMatcher<'tc> {
    /// Create a new [PatMatcher].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Verify that the given set of members corresponding to the given
    /// patterns, all bind distinct names.
    fn verify_members_are_bound_once(&self, members: &[PatMember]) -> TcResult<()> {
        let mut names: HashSet<Identifier> = HashSet::new();

        for PatMember { member, pat } in members.iter() {
            if names.contains(&member.name()) {
                return Err(TcError::IdentifierBoundMultipleTimes {
                    name: member.name(),
                    pat: *pat,
                });
            } else {
                names.insert(member.name());
            }
        }

        Ok(())
    }

    /// Convert a list of [Member]s with their corresponding [PatId] into map
    /// between the [Member] binding name, the type of the member and the
    /// [PatId].
    ///
    /// **Note**: This function assumes that the uniqueness of the members has
    /// been checked before creating the map.
    fn map_variables_to_terms(
        &self,
        members: &[PatMember],
    ) -> HashMap<Identifier, (TermId, PatId)> {
        members
            .iter()
            .map(|PatMember { member, pat }| (member.name(), (member.ty(), *pat)))
            .collect()
    }

    /// Function to check that the inner patterns of a [Pat::Or] adhere to the
    /// following rule:
    ///
    /// - For every inner pattern, the resultant members must be equivalent in
    ///   terms of name and type.
    fn pat_members_match(&self, members: &[(Vec<PatMember>, PatId)]) -> TcResult<()> {
        let member_maps = members
            .iter()
            .map(|(members, pat)| (self.map_variables_to_terms(members), pat))
            .collect_vec();

        let mut err = None;

        // @@Todo: make this a macro
        let mut append_err = |tc_err| {
            if err.is_some() {
                self.diagnostics().add_error(tc_err);
            } else {
                err = Some(tc_err);
            }
        };

        // Take the first member as we'll use it for our comparison
        let mut member_binds = HashSet::new();

        for (lhs_members, lhs_pat) in member_maps.clone().iter() {
            member_binds = lhs_members.keys().copied().collect::<HashSet<Identifier>>();

            // Compute the difference in `name` keys, if there exists a
            // difference then we add this as an error on the pattern.
            for (rhs_members, rhs_pat) in member_maps.iter() {
                // Skip comparing the same pattern
                if lhs_pat == rhs_pat {
                    continue;
                }

                // We want to find the largest member and report that that member doesn't
                // contain the binds...
                let cur_binds = rhs_members.keys().copied().collect::<HashSet<Identifier>>();
                let mut diff = member_binds.difference(&cur_binds).peekable();

                // If there is at least one discrepancy, we want to generate the report already
                if diff.peek().is_some() {
                    append_err(TcError::MissingPatternBounds {
                        pat: **rhs_pat,
                        bounds: diff.copied().collect_vec(),
                    });
                }
            }
        }

        // If at least one error occurred, then we return the error
        if let Some(err) = err {
            return Err(err);
        }

        // Now we need to verify that all of the member binds are of the
        // same type...
        for bind in member_binds {
            let shared_terms =
                member_maps.iter().map(|(map, _)| map.get(&bind).unwrap()).copied().collect_vec();
            self.unifier().unify_pat_terms(shared_terms)?;
        }

        Ok(())
    }

    /// Utility for creating the captured member when a spread pattern
    /// has a binding. This takes in all of the members that were captured
    /// when erasing the `...` from the constructor or tuple and creates
    /// a new member that is now visible with scope with the specified `name`.
    ///
    /// The type of the member is a tuple that contains the members that were
    /// captured from the `...` erasure with their associated names and type
    /// values.
    fn create_tuple_member_from_captured_members_in_spread_pat(
        &self,
        items: Vec<(PatArg, TermId, Option<TermId>)>,
        name: Identifier,
        original_id: PatId,
    ) -> TcResult<Option<PatMember>> {
        let members = self.builder().create_args(
            items.iter().map(|(member, ty, value)| ArgOld {
                name: member.name,
                value: value.unwrap_or(self.builder().create_rt_term(*ty)),
            }),
            ParamOrigin::Tuple,
        );

        let inferred_term = self.builder().create_tuple_lit_term(members);

        let captured_members = self
            .builder()
            .create_pat_args(items.into_iter().map(|(arg, _, _)| arg), ParamOrigin::Tuple);
        let id = self.pat_store().create(Pat::Tuple(captured_members));

        // We need to copy over the location of the pattern from the spread pattern to
        // this one so in-case it is used for error reporting purposes...
        self.location_store().copy_location(original_id, id);

        Ok(Some(PatMember {
            member: Member::variable(name, Mutability::Immutable, inferred_term, inferred_term),
            pat: id,
        }))
    }

    /// Find a spread pattern within the provided [PatArgsId].
    fn find_spread_pattern_in_members(
        &self,
        members: PatArgsId,
    ) -> Option<(usize, Option<Identifier>, PatId)> {
        let members = self.reader().get_pat_args_owned(members);

        for (index, member) in members.positional().iter().enumerate() {
            if let Pat::Spread(SpreadPat { name, .. }) = self.reader().get_pat(member.pat) {
                return Some((index, name, member.pat));
            }
        }

        None
    }

    /// Function that will `erase` a spread pattern from the given constructor
    /// based on the arguments in the constructor. The constructor can
    /// either be a struct or an [hash_types::EnumVariant] or a
    /// [hash_types::ConstructedTerm].
    ///
    /// In the case of the struct literal, all of the field names should have
    /// been resolved since this happens when the struct field is validated.
    /// So any fields that are not captured by the specified arguments are
    /// then appended into a `named` tuple that is created as the captured
    /// variable group. For example:
    ///
    /// ```ignore
    /// Foo := struct(
    ///     age: i32,
    ///     sex: char,
    ///     name: str,
    /// );
    ///
    /// x := Foo::default();
    ///
    /// Foo(age, ...other) := x; // other: (name: str, sex: char)
    /// ```
    ///
    /// In the case of an enum variant which is un-named, the same logic is
    /// applied to un-named tuples, where only a collection of the fields is
    /// captured. Any members that are not specified are captured by an
    /// un-named tuple as a side product that can be accessed if the spread
    /// pattern specifies a bind. For example:
    ///
    /// ```ignore
    /// Foo := enum(
    ///     Bar(i32, str, char),
    /// );
    ///
    /// x := Foo::default();
    ///
    /// Foo::Bar(num, ...other) := x; // other: (str, char)
    /// ```
    ///
    /// Additionally, all of the fields that are not specified by the enum or
    /// struct are now filled in as *wildcard* patterns, essentially being
    /// ignored.
    fn maybe_erase_spread_pat_from_constructor(
        &self,
        pat: PatId,
        ConstructorPat { args, subject }: ConstructorPat,
    ) -> TcResult<Option<PatMember>> {
        let reader = self.reader();

        // Utility for creating a wildcard pattern since this is a
        // common operation.
        let wildcard_pat = || self.pat_store().create(Pat::Wild);

        let spread_pat = self.find_spread_pattern_in_members(args);
        if spread_pat.is_none() {
            return Ok(None);
        }
        let (_, name, spread_id) = spread_pat.unwrap();

        // @@Todo: deal with enum variants
        let subject_members = match self.oracle().term_as_struct_def(subject).unwrap().fields {
            StructFields::Explicit(fields) => fields,
            // @@ErrorReporting: this should be a tc panic
            _ => unreachable!(),
        };

        let pat_args = reader.get_pat_args_owned(args);
        let ty_members = reader.get_params_owned(subject_members);

        // Build a collection of members that are to be inserted into the new tuple term
        let mut new_members = vec![];
        let mut captured_members = vec![];

        for (member_pos, ty_member) in ty_members.positional().iter().enumerate() {
            if let Some(name) = ty_member.name {
                if let Some((index, arg)) = pat_args.get_by_name(name) {
                    new_members.push((*arg, index));
                } else {
                    let item = PatArg { name: Some(name), pat: wildcard_pat() };

                    new_members.push((item, member_pos));

                    // We need to save the index of the member that was captured so
                    // we can create a type from it later
                    captured_members.push((item, ty_member.ty, ty_member.default_value));
                }
            }
        }

        let new_pat_members = self
            .builder()
            .create_pat_args(new_members.into_iter().map(|(arg, _)| arg), ParamOrigin::Tuple);

        // @@Todo: remove this modification!
        self.pat_store()
            .set(pat, Pat::Constructor(ConstructorPat { subject, args: new_pat_members }));

        // If the spread pattern has a bind, then we need to also create the new tuple
        // type and return it as a bound member to that value.
        name.map_or(Ok(None), |name| {
            self.create_tuple_member_from_captured_members_in_spread_pat(
                captured_members,
                name,
                spread_id,
            )
        })
    }

    /// Function use to erase any spread patterns that are present within
    /// [Pat::Tuple] and [Pat::Constructor]. Erasing means turning the spread
    /// patterns into a collection of wildcard fields that fill any missing
    /// field that is not specified by the pattern.
    ///
    /// N.B. This modifies the stored pattern associated with the provided
    /// [PatId].
    fn maybe_erase_spread_pat_from_tuple(
        &self,
        pat: PatId,
        members: PatArgsId,
        subject: TermId,
    ) -> TcResult<Option<PatMember>> {
        let reader = self.reader();

        // Utility for creating a wildcard pattern since this is a
        // common operation.
        let wildcard_pat = || self.pat_store().create(Pat::Wild);

        let spread_pat = self.find_spread_pattern_in_members(members);
        if spread_pat.is_none() {
            return Ok(None);
        }

        let (pos, name, spread_id) = spread_pat.unwrap();

        // In this situation, we need to collect all of the members within
        // the `subject` tuple type and build a map of where we essentially
        // need to fill in the missing fields.
        let ty_members_id =
            self.typer().infer_params_ty_of_tuple_term(subject)?.unwrap_or_else(|| {
                tc_panic!(subject, self, "This term `{}` is not a tuple", self.for_fmt(subject))
            });

        let pat_members = reader.get_pat_args_owned(members);
        let ty_members = reader.get_params_owned(ty_members_id);

        // Fast track if the members of the pattern have a greater length
        // than the type members
        if ty_members.len() < pat_members.len() {
            let filtered_members = pat_members
                .into_positional()
                .into_iter()
                .enumerate()
                .filter(|(index, _)| *index != pos)
                .map(|(_, arg)| arg);

            // So now we need to update the stored pattern with this newly constructed
            // one
            let new_pat_members =
                self.builder().create_pat_args(filtered_members, ParamOrigin::Tuple);

            // @@Todo: Remove this modification !
            self.pat_store().set(pat, Pat::Tuple(new_pat_members));

            return name.map_or(Ok(None), |name| {
                self.create_tuple_member_from_captured_members_in_spread_pat(
                    vec![],
                    name,
                    spread_id,
                )
            });
        }

        // - If `pat_members` and `ty_members` are named, `pat_members` field names must
        //   all be present within `ty_member` fields.
        let ty_members_named = ty_members.positional().iter().any(|member| member.name.is_some());

        // If the type members are named but the pattern members are not, we want to
        // "infer" their names wherever possible. This is done by looking at
        // each argument, and if it is a bind which is present in the type, we
        // add a name to it.
        let inferred_pat_members = if ty_members_named {
            let inferred_pat_args_id = self.builder().create_pat_args(
                pat_members.positional().iter().map(|arg| {
                    if arg.name.is_none() {
                        if let Pat::Binding(binding_pat) = reader.get_pat(arg.pat) {
                            if ty_members.get_by_name(binding_pat.name).is_some() {
                                return PatArg { name: Some(binding_pat.name), ..*arg };
                            }
                        }
                    }
                    *arg
                }),
                pat_members.origin(),
            );
            self.reader().get_pat_args_owned(inferred_pat_args_id)
        } else {
            pat_members
        };

        // If the tuple pattern is a single spread pattern, it inherits the naming
        // conventions of the type that is being matched.
        let pat_members_named = if inferred_pat_members.len() == 1 {
            ty_members_named
        } else {
            inferred_pat_members.positional().iter().any(|member| member.name.is_some())
        };

        // Build a collection of members that are to be inserted into the new tuple term
        let mut new_members = vec![];
        let mut captured_members = vec![];

        match (ty_members_named, pat_members_named) {
            // Both type and pattern is named
            (true, true) => {
                // verify all specified pat member names exist within the
                // type...
                validate_named_params_match(
                    &ty_members,
                    &inferred_pat_members,
                    ParamListKind::PatArgs(members),
                    subject,
                )?;

                for (member_pos, ty_member) in ty_members.positional().iter().enumerate() {
                    if let Some(name) = ty_member.name {
                        if let Some((index, arg)) = inferred_pat_members.get_by_name(name) {
                            new_members.push((*arg, index));
                        } else {
                            let item = PatArg { name: Some(name), pat: wildcard_pat() };

                            new_members.push((item, member_pos));

                            // We need to save the index of the member that was captured so
                            // we can create a type from it later
                            captured_members.push((item, ty_member.ty, ty_member.default_value));
                        }
                    }
                }
            }
            // Either both un-named, or one of them is named. However, it doesn't
            // matter because we can fallback to using positional resolution logic.
            //
            // If `ty_members` is named, and `pat_members` is un-named then all ty_member
            // fields will be coerced into un-named fields. The captured tuple members
            // preserve the names that they captured.
            //
            // Similarly, if `ty_members` is un-named, and `pat_members` are named, the
            // fields will preserve there name fields, but the captured members by the
            // spread pattern do not inherit any names since we don't know what they
            // should be called.
            _ => {
                // Emit a warning since we're coercing this types members into named
                // fields into un-named fields.
                if ty_members_named && !pat_members_named {
                    self.diagnostics().add_warning(TcWarning::NamedTupleCoercion {
                        original: subject,
                        coerced_into: pat,
                    });
                }

                let mut spread_offset = 0;

                // Determine the boundary of which the spread pattern captures elements
                // for, this is redundant if the tuple has named fields.
                let (start, end) = if pos == inferred_pat_members.len() - 1 {
                    (pos, ty_members.len())
                } else {
                    (pos, (ty_members.len() - (inferred_pat_members.len() - pos)))
                };

                for (member_pos, ty_member) in ty_members.positional().iter().enumerate() {
                    // The only valid case is if the `member_pos` is currently between
                    // the starting index of the spread pattern and the number of members
                    // already captured... if it is in this range then it means that we
                    // must be creating a new wildcard pat
                    if (start..=end).contains(&member_pos) {
                        let item = PatArg { name: ty_member.name, pat: wildcard_pat() };
                        new_members.push((item, member_pos));

                        // We need to save the index of the member that was captured so
                        // we can create a type from it later
                        captured_members.push((item, ty_member.ty, ty_member.default_value));
                    } else {
                        // in this case we just add the member that is in `pat_members` at
                        // the adjusted index
                        let index = if member_pos < start {
                            member_pos
                        } else {
                            spread_offset += 1;
                            min(pos + spread_offset, inferred_pat_members.len() - 1)
                        };

                        let mut member = inferred_pat_members.positional()[index];

                        // The member inherits the name of the tuple type member if the name
                        // exists...
                        if let Some(name) = ty_member.name {
                            assert!(member.name.is_none());

                            member.name = Some(name);
                        }

                        new_members.push((member, index));
                    }
                }
            }
        }

        // Now we need to create the new tuple pattern and then update the store
        new_members.sort_by(|l, r| l.1.cmp(&r.1));

        let new_pat_members = self
            .builder()
            .create_pat_args(new_members.into_iter().map(|(arg, _)| arg), ParamOrigin::Tuple);

        // @@Todo: remove this modification!
        self.pat_store().set(pat, Pat::Tuple(new_pat_members));

        // If the spread pattern has a bind, then we need to also create the new tuple
        // type and return it as a bound member to that value.
        name.map_or(Ok(None), |name| {
            self.create_tuple_member_from_captured_members_in_spread_pat(
                captured_members,
                name,
                spread_id,
            )
        })
    }

    /// Match a [Pat::Tuple] with a subject term, and extract bound members.
    fn match_tuple_pat_with_term(
        &self,
        pat: PatId,
        members: PatArgsId,
        subject: TermId,
    ) -> TcResult<Option<Vec<PatMember>>> {
        // Get the term of the tuple and try to unify it with the subject:
        let tuple_term = self.typer().get_term_of_pat(pat)?;

        match self.unifier().unify_terms(tuple_term, subject) {
            Ok(_) => {
                let subject_params_id = self
                    .typer()
                    .infer_params_ty_of_tuple_term(subject)?
                    .unwrap_or_else(|| tc_panic!(subject, self, "This is not a tuple term."));
                self.match_pat_args_with_subject_params(members, subject_params_id)
            }
            Err(_) => Ok(None),
        }
    }

    /// Match a [Pat::Constructor] with a subject term. Walk all of the inner
    /// patterns and collect bound members.
    fn match_constructor_pat_with_term(
        &self,
        ConstructorPat { args, subject }: ConstructorPat,
    ) -> TcResult<Option<Vec<PatMember>>> {
        // get the subject params
        let possible_subject_params = self.typer().infer_constructor_of_nominal_term(subject)?;

        if possible_subject_params.is_empty() {
            return Err(TcError::NoConstructorOnType { subject });
        }

        // @@Verify: Otherwise we get the first one, it should not be possible for
        // another situation here...?
        let (_, subject_params_id) = possible_subject_params[0];

        self.match_pat_args_with_subject_params(args, subject_params_id)
    }

    fn match_pat_args_with_subject_params(
        &self,
        pat_args_id: PatArgsId,
        subject_params_id: ParamsId,
    ) -> TcResult<Option<Vec<PatMember>>> {
        let subject_params = self.reader().get_params_owned(subject_params_id);
        let pat_args = self.reader().get_pat_args_owned(pat_args_id);

        // For each param pair: accumulate the bound members
        let mut bound_members = vec![];

        for (index, param) in subject_params.positional().iter().enumerate() {
            let arg = if let Some(name) = param.name {
                if let Some((_, arg)) = pat_args.get_by_name(name) {
                    arg
                } else {
                    &pat_args.positional()[index]
                }
            } else {
                &pat_args.positional()[index]
            };

            let param_value =
                param.default_value.unwrap_or_else(|| self.builder().create_rt_term(param.ty));

            // If the argument has a name, and if the pattern is not a bind, i.e. it's just
            // setting the name, so that we don't add it twice then add the name
            // to the scope.
            if let Some(name) = arg.name && !self.reader().get_pat(arg.pat).is_bind() {
                bound_members.push(PatMember {
                    member: Member::variable(name, Mutability::Immutable, param.ty, param_value),
                    pat: arg.pat,
                });
            }

            bound_members.extend(
                self.match_pat_with_term_and_extract_binds(arg.pat, param_value)?
                    .into_iter()
                    .flatten()
                    .collect_vec(),
            );
        }

        Ok(Some(bound_members))
    }

    /// Match a [Pat::List] with the subject term, walk all inner patterns
    /// and extract bound members.
    ///
    /// @@Todo: if the inner parameter is a `...` pattern, we need to pass
    /// in the `List<term>` type.
    fn match_list_pat_with_term(
        &self,
        ListPat { list_element_ty, element_pats }: ListPat,
    ) -> TcResult<Option<Vec<PatMember>>> {
        // We need to collect all of the binds from the inner patterns of
        // the list
        let params = self.reader().get_pat_args_owned(element_pats).clone();

        let mut bound_members = vec![];
        let shared_term = self.builder().create_rt_term(list_element_ty);

        for param in params.positional().iter() {
            match self.match_pat_with_term_and_extract_binds(param.pat, shared_term)? {
                Some(members) => {
                    bound_members.extend(members);
                }
                // If one of them fails, we should fail as a whole
                None => return Ok(None),
            }
        }

        Ok(Some(bound_members))
    }

    /// Match a [Pat::Spread] with the subject type. The [Pat::Spread] must
    /// be within a [Pat::List] since spread patterns in other structural
    /// patterns are already eliminated at this stage.
    fn match_spread_pat_with_term(
        &self,
        id: PatId,
        SpreadPat { name }: SpreadPat,
        subject_ty: TermId,
    ) -> TcResult<Option<Vec<PatMember>>> {
        match name {
            Some(name) => {
                // Since `pat_ty` will be `List<T = Unresolved>`, we need to create a new
                // `List<T = term_ty_id>` and perform a unification...
                let list_inner_ty = self.core_defs().list_ty_fn();
                let builder = self.builder();

                let pat_ty = builder.create_app_ty_fn_term(
                    list_inner_ty,
                    builder
                        .create_args([builder.create_nameless_arg(subject_ty)], ParamOrigin::TyFn),
                );

                let rt_term = self.builder().create_rt_term(pat_ty);

                let TermValidation { simplified_term_id, term_ty_id } =
                    self.validator().validate_term(rt_term)?;

                Ok(Some(vec![PatMember {
                    member: Member::variable(
                        name,
                        Mutability::Immutable,
                        term_ty_id,
                        simplified_term_id,
                    ),
                    pat: id,
                }]))
            }
            _ => Ok(Some(vec![])),
        }
    }

    /// Match a [Pat::Mod] with the subject term, and then extract
    /// all of the bound members that are specified.
    fn match_mod_pat_with_term(
        &self,
        ModPat { members }: ModPat,
        subject: TermId,
    ) -> TcResult<Option<Vec<PatMember>>> {
        let members = self.reader().get_pat_args_owned(members).clone();

        let mut bound_members = vec![];

        //  Here we have to basically try to access the given members using ns access...
        for member in members.positional() {
            let PatArg { name, pat } = *member;

            // Before we recurse into the inner pattern, we need to
            // create an access term that accesses `name` from the
            // current term... and then we recurse into pattern
            let term = self.builder().create_access(subject, name.unwrap(), AccessOp::Namespace);

            // If one of them fails, then we have to fail as a whole
            match self.match_pat_with_term_and_extract_binds(pat, term)? {
                Some(inner_members) => bound_members.extend(inner_members),
                None => return Ok(None),
            }
        }

        Ok(Some(bound_members))
    }

    /// Match a [Pat::Or] with the subject term. Traverse all of the inner
    /// members of the [Pat::Or], and verify that each of the child patterns
    /// binds the same members, and each member has the same type.
    fn match_or_pat_with_term(
        &self,
        pats: &[PatId],
        subject: TermId,
    ) -> TcResult<Option<Vec<PatMember>>> {
        // Traverse all of the inner patterns within the `or` pattern, create a
        // map between the member names that are produced and the type of the
        // pattern... Then we want to ensure all of them are equal
        let pat_members = pats
            .iter()
            .map(|pat| {
                self.match_pat_with_term_and_extract_binds(*pat, subject)
                    .map(|m| m.map(|t| (t, *pat)))
            })
            .flatten_ok()
            .collect::<TcResult<Vec<_>>>()?;

        // One of the cases never matches with the subject if the length is not the same
        if pat_members.len() != pats.len() {
            return Ok(None);
        }

        self.pat_members_match(&pat_members)?;

        // Since all verification happens, we can now return the first member
        // since we know that all of the types are the same, and all the binds
        // will be in scope, regardless of which pattern is matched at runtime
        Ok(Some(pat_members[0].0.clone()))
    }

    /// Match the given pattern with the given term, returning a potential list
    /// of extracted `binds` that the pattern describes.
    ///
    /// @@Fixme Re-work level 0 unification (i.e. should never work when Rts are
    /// involved), and that this function should unify the types, rather
    /// than the values, of the pattern and term.
    fn match_pat_with_term_and_extract_binds(
        &self,
        pat_id: PatId,
        term_id: TermId,
    ) -> TcResult<Option<Vec<PatMember>>> {
        let TermValidation { simplified_term_id, term_ty_id } =
            self.validator().validate_term(term_id)?;

        let reader = self.reader();

        // we need to erase  `...` here for tuples and constructors
        let captured_member = match reader.get_pat(pat_id) {
            Pat::Tuple(members) => {
                self.maybe_erase_spread_pat_from_tuple(pat_id, members, term_id)?
            }
            Pat::Constructor(constructor) => {
                self.maybe_erase_spread_pat_from_constructor(pat_id, constructor)?
            }
            _ => None,
        };

        // re-read the pattern since it may of been modified
        let pat = reader.get_pat(pat_id);
        let pat_ty = self.typer().infer_ty_of_pat(pat_id)?;

        let _ = self.unifier().unify_terms(pat_ty, term_ty_id)?;

        let mut bound_members = match pat {
            // Binding: Add the binding as a member
            Pat::Binding(binding) => Ok(Some(vec![PatMember {
                member: Member::variable(
                    binding.name,
                    binding.mutability,
                    term_ty_id,
                    simplified_term_id,
                ),
                pat: pat_id,
            }])),

            // We don't actually do anything here with the spread pattern since this should happen
            // at either the `list`, `tuple` or `constructor level. If it does not, then this
            // is an invariant since the spread pattern shouldn't be here.
            Pat::Spread(spread_pat) => {
                self.match_spread_pat_with_term(pat_id, spread_pat, term_ty_id)
            }
            Pat::Access(AccessPat { subject, property }) => {
                let subject_term = self.typer().get_term_of_pat(subject)?;
                let term = self.builder().create_ns_access(subject_term, property);

                match self.unifier().unify_terms(term, simplified_term_id) {
                    Ok(_) => Ok(Some(vec![])),
                    Err(_) => Ok(None),
                }
            }
            Pat::Const(ConstPat { term, .. }) => {
                match self.unifier().unify_terms(term, simplified_term_id) {
                    Ok(_) => Ok(Some(vec![])),
                    Err(_) => Ok(None),
                }
            }
            // No bindings in range patterns
            //
            // @@Improvement: we could add a check in the future that tries to see if this is a
            // useful match.
            Pat::Range(_) => Ok(Some(vec![])),
            // No bindings but always matches
            Pat::Wild => Ok(Some(vec![])),
            // Lit: Unify the literal with the subject
            Pat::Lit(lit_term) => match self.unifier().unify_terms(lit_term, simplified_term_id) {
                Ok(_) => Ok(Some(vec![])),
                Err(_) => Ok(None),
            },

            Pat::Mod(mod_pat) => self.match_mod_pat_with_term(mod_pat, term_id),
            Pat::Tuple(members) => {
                self.match_tuple_pat_with_term(pat_id, members, simplified_term_id)
            }
            Pat::Constructor(constructor) => self.match_constructor_pat_with_term(constructor),
            Pat::List(list) => self.match_list_pat_with_term(list),
            Pat::Or(pats) => self.match_or_pat_with_term(&pats, simplified_term_id),
            Pat::If(IfPat { pat, .. }) => {
                // Recurse to inner, but never say it is redundant:
                match self.match_pat_with_term_and_extract_binds(pat, term_id)? {
                    Some(result) => Ok(Some(result)),
                    None => Ok(Some(vec![])),
                }
            }
        }?;

        // If the there are bound members, then we need to push the possible
        // bound member from spread pattern erasure...
        if let Some(member) = captured_member {
            if let Some(members) = bound_members.as_mut() {
                members.push(member)
            }
        }

        // Here, we verify that the produced members from the pattern are unique...
        if let Some(members) = bound_members {
            self.verify_members_are_bound_once(&members)?;

            Ok(Some(members))
        } else {
            Ok(None)
        }
    }

    /// Match the given pattern with the given term, returning
    /// [`Vec<Member>`] if the pattern matches (with a list of bound
    /// members), or [`None`] if it doesn't match. If the types mismatch, it
    /// returns an error.
    pub fn match_pat_with_term(
        &self,
        pat_id: PatId,
        term_id: TermId,
    ) -> TcResult<Option<Vec<Member>>> {
        self.match_pat_with_term_and_extract_binds(pat_id, term_id).map(|members| {
            members.map(|inner| inner.into_iter().map(|pat_member| pat_member.member).collect())
        })
    }
}
