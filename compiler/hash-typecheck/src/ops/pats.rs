//! Functionality related to pattern matching.

use std::{
    cmp::min,
    collections::{HashMap, HashSet},
};

use hash_ast::ast::{ParamOrigin, SpreadPatOrigin};
use hash_reporting::diagnostic::Diagnostics;
use hash_source::identifier::Identifier;
use hash_utils::store::Store;
use itertools::Itertools;

use super::{
    params::{pair_args_with_params, validate_named_params_match},
    AccessToOps,
};
use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::tc_panic,
        params::ParamListKind,
        warning::TcWarning,
    },
    ops::validate::TermValidation,
    storage::{
        pats::{PatArgsId, PatId},
        primitives::{
            AccessOp, AccessPat, Arg, BindingPat, ConstPat, ConstructorPat, IfPat, ListPat, Member,
            ModPat, Mutability, Param, Pat, PatArg, SpreadPat, Visibility,
        },
        terms::TermId,
        AccessToStorage, StorageRef,
    },
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

impl<'tc> PatMatcher<'tc> {
    /// Create a new [PatMatcher].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Internal function to infer a pattern from a `Param`.
    fn param_to_pat(&self, param: &Param) -> PatArg {
        let Param { name, default_value, .. } = param;
        let pat = self.builder().create_constant_pat(default_value.unwrap());

        PatArg { name: *name, pat }
    }

    /// Internal function to verify that the members that are produced from
    /// traversing a pattern are only binded once.
    pub fn verify_members_are_bound_once(&self, members: &[(Member, PatId)]) -> TcResult<()> {
        let mut names: HashSet<Identifier> = HashSet::new();

        for (member, pat) in members.iter() {
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
        members: &[(Member, PatId)],
    ) -> HashMap<Identifier, (TermId, PatId)> {
        members.iter().map(|(member, pat)| (member.name(), (member.ty(), *pat))).collect()
    }

    /// Function to check that the inner patterns of a [Pat::Or] adhere to the
    /// following rule:
    ///
    /// - For every inner pattern, the resultant members must be equivalent in
    ///   terms of name and type.
    fn pat_members_match(&self, members: &[(Vec<(Member, PatId)>, PatId)]) -> TcResult<()> {
        let member_maps = members
            .iter()
            .map(|(members, pat)| (self.map_variables_to_terms(members), pat))
            .collect_vec();

        // Take the first member as we'll use it for our comparison
        let mut members = member_maps.iter();
        let (first_map, first_pat_id) = members.next().unwrap();
        let first_binds = first_map.keys().copied().collect::<HashSet<Identifier>>();

        // Compute the difference in `name` keys, if there exists a
        // difference then we can immediately report the error and abort...
        //
        // @@ErrorReporting: It would be nice to produce multiple errors here
        for (member, cur_pat_id) in members {
            // We want to find the largest member and report that that member doesn't
            // contain the binds...
            let cur_binds = member.keys().copied().collect::<HashSet<Identifier>>();

            let (mut diff, pat) = if first_binds.len() > cur_binds.len() {
                (first_binds.difference(&cur_binds).peekable(), *cur_pat_id)
            } else {
                (cur_binds.difference(&first_binds).peekable(), *first_pat_id)
            };

            // If there is at-least one discrepancy, we want to generate the report already
            if diff.peek().is_some() {
                return Err(TcError::MissingPatternBounds {
                    pat: *pat,
                    bounds: diff.copied().collect_vec(),
                });
            }
        }

        // Now we need to verify that all of the member binds are of the
        // same type...
        for bind in first_binds {
            let shared_terms =
                member_maps.iter().map(|(map, _)| map.get(&bind).unwrap()).copied().collect_vec();

            self.unifier().unify_pat_terms(shared_terms)?;
        }

        Ok(())
    }

    /// Utility for creating the captured member when a spread pattern
    /// has a binding. This takes in
    fn create_pat_from_captured_members(
        &self,
        items: Vec<(PatArg, TermId, Option<TermId>)>,
        name: Identifier,
        original_id: PatId,
    ) -> TcResult<Option<(Member, PatId)>> {
        // If there is only one captured element, we turn this into a
        // bind pattern rather than being a tuple...
        let (id, inferred_term, value) = if items.len() == 1 {
            // Create the binding that puts the
            let id = self.pat_store().create(Pat::Binding(BindingPat {
                name,
                mutability: Mutability::Immutable,
                visibility: Visibility::Private,
            }));

            (id, items[0].1, items[0].2.unwrap_or(items[0].1))
        } else {
            // Now we also need to infer the type of the tuple
            let members = self.builder().create_args(
                items.iter().map(|(member, value, _)| Arg { name: member.name, value: *value }),
                ParamOrigin::Tuple,
            );

            let inferred_term = self.builder().create_tuple_lit_term(members);

            let captured_members = self
                .builder()
                .create_pat_args(items.into_iter().map(|(arg, _, _)| arg), ParamOrigin::Tuple);
            let id = self.pat_store().create(Pat::Tuple(captured_members));

            (id, inferred_term, inferred_term)
        };

        // We need to copy over the location of the pattern from the spread pattern to
        // this one so in-case it is used for error reporting purposes...
        self.location_store().copy_location(original_id, id);

        Ok(Some((Member::variable(name, Mutability::Immutable, inferred_term, value), id)))
    }

    fn maybe_erase_spread_pat_from_constructor(
        &self,
        _pat: PatId,
        _constructor: ConstructorPat,
        _subject: TermId,
    ) -> TcResult<Option<(Member, PatId)>> {
        let _reader = self.reader();
        // @@Todo: implement spread pattern erasure for constructor patterns
        Ok(None)
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
    ) -> TcResult<Option<(Member, PatId)>> {
        let reader = self.reader();

        // Utility for creating a wildcard pattern since this is a
        // common operation.
        let wildcard_pat = || self.pat_store().create(Pat::Wild);

        let pat_members = reader.get_pat_args_owned(members);

        // Check if the members has a `...` pattern and then if so
        // we will need to proceed and erase it.
        let mut spread_pat = None;

        for (index, member) in pat_members.positional().iter().enumerate() {
            if let Pat::Spread(SpreadPat { name, .. }) = reader.get_pat(member.pat) {
                if spread_pat.is_some() {
                    tc_panic!(
                        member.pat,
                        self,
                        "found multiple spread patterns within tuple pattern"
                    )
                }

                spread_pat = Some((index, name, member.pat));
            }
        }

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

            self.pat_store().set(pat, Pat::Tuple(new_pat_members));

            return name.map_or(Ok(None), |name| {
                self.create_pat_from_captured_members(vec![], name, spread_id)
            });
        }

        // - If `pat_members` and `ty_members` are named, `pat_members` field names must
        //   all be present within `ty_member` fields.
        let ty_members_named = ty_members.positional().iter().any(|member| member.name.is_some());
        let pat_members_named = pat_members.positional().iter().any(|member| member.name.is_some());

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
                    &pat_members,
                    ty_members_id,
                    ParamListKind::PatArgs(members),
                    subject,
                )?;

                for (member_pos, ty_member) in ty_members.positional().iter().enumerate() {
                    if let Some(name) = ty_member.name {
                        if let Some((index, arg)) = pat_members.get_by_name(name) {
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
                let (start, end) = if pos == pat_members.len() - 1 {
                    (pos, ty_members.len())
                } else {
                    (pos, (ty_members.len() - (pat_members.len() - pos)))
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
                            min(pos + spread_offset, pat_members.len() - 1)
                        };

                        let mut member = pat_members.positional()[index];

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

        self.pat_store().set(pat, Pat::Tuple(new_pat_members));

        // If the spread pattern has a bind, then we need to also create the new tuple
        // type and return it as a bound member to that value.
        name.map_or(Ok(None), |name| {
            self.create_pat_from_captured_members(captured_members, name, spread_id)
        })
    }

    /// Match a [Pat::Tuple] with a subject term, and extract bound members.
    fn match_tuple_pat_with_term(
        &self,
        pat: PatId,
        members: PatArgsId,
        subject: TermId,
    ) -> TcResult<Option<Vec<(Member, PatId)>>> {
        // Get the term of the tuple and try to unify it with the subject:
        let tuple_term = self.typer().get_term_of_pat(pat)?;

        match self.unifier().unify_terms(tuple_term, subject) {
            Ok(_) => {
                let tuple_pat_args = self.reader().get_pat_args_owned(members).clone();

                // We get the subject tuple's parameters:
                let subject_params_id = self
                    .typer()
                    .infer_params_ty_of_tuple_term(subject)?
                    .unwrap_or_else(|| tc_panic!(subject, self, "This is not a tuple term."));

                let subject_params = self.reader().get_params_owned(subject_params_id).clone();

                // For each param pair: accumulate the bound members
                let bound_members = subject_params
                    .positional()
                    .iter()
                    .zip(tuple_pat_args.positional())
                    .map(|(param, pat_param)| {
                        let param_value = param
                            .default_value
                            .unwrap_or_else(|| self.builder().create_rt_term(param.ty));

                        // @@Todo: retain information about useless patterns
                        Ok(self
                            .match_pat_with_term_and_extract_binds(pat_param.pat, param_value)?
                            .into_iter()
                            .flatten()
                            .collect::<Vec<_>>())
                    })
                    .flatten_ok()
                    .collect::<TcResult<Vec<_>>>()?;

                Ok(Some(bound_members))
            }
            Err(_) => Ok(None),
        }
    }

    /// Match a [Pat::Constructor] with a subject term. Walk all of the inner
    /// patterns and collect bound members.
    fn match_constructor_pat_with_term(
        &self,
        id: PatId,
        ConstructorPat { args, .. }: ConstructorPat,
        subject: TermId,
    ) -> TcResult<Option<Vec<(Member, PatId)>>> {
        // Get the term of the constructor and try to unify it with the subject:
        let constructor_term = self.typer().get_term_of_pat(id)?;

        let pat_args = self.typer().infer_args_of_pat_args(args)?;
        let constructor_args = self.reader().get_pat_args_owned(args).clone();

        let possible_params = self.typer().infer_constructors_of_nominal_term(subject)?;

        for (_, params) in possible_params {
            let subject_params = self.reader().get_params_owned(params).clone();

            match pair_args_with_params(
                &subject_params,
                &constructor_args,
                params,
                pat_args,
                |param| self.param_to_pat(param),
                subject,
                id,
            ) {
                Ok(members) => {
                    let bound_members = members
                        .into_iter()
                        .map(|(param, arg)| {
                            let param_value = param
                                .default_value
                                .unwrap_or_else(|| self.builder().create_rt_term(param.ty));

                            Ok(self
                                .match_pat_with_term_and_extract_binds(arg.pat, param_value)?
                                .into_iter()
                                .flatten()
                                .collect::<Vec<_>>())
                        })
                        .flatten_ok()
                        .collect::<TcResult<Vec<_>>>()?;

                    // @@Refactor: we need to verify that the members are declared once.
                    // Since this happens at the bottom of the
                    // function already, it would be nice to
                    // factor out this step to be at the bottom or factor out constructor
                    // pattern checking into a separate
                    // function.
                    self.verify_members_are_bound_once(&bound_members)?;
                    return Ok(Some(bound_members));
                }
                Err(_) => continue,
            }
        }

        Err(TcError::NoConstructorOnType { subject: constructor_term })
    }

    /// Match a [Pat::List] with the subject term, walk all inner patterns
    /// and extract bound members.
    ///
    /// @@Todo: if the inner parameter is a `...` pattern, we need to pass
    /// in the `List<term>` type.
    fn match_list_pat_with_term(
        &self,
        ListPat { term, inner }: ListPat,
    ) -> TcResult<Option<Vec<(Member, PatId)>>> {
        // We need to collect all of the binds from the inner patterns of
        // the list
        let params = self.reader().get_pat_args_owned(inner).clone();

        let mut bound_members = vec![];
        let shared_term = self.builder().create_rt_term(term);

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
        SpreadPat { name, origin }: SpreadPat,
        subject_ty: TermId,
    ) -> TcResult<Option<Vec<(Member, PatId)>>> {
        assert_eq!(origin, SpreadPatOrigin::List);

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

                Ok(Some(vec![(
                    Member::variable(name, Mutability::Immutable, term_ty_id, simplified_term_id),
                    id,
                )]))
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
    ) -> TcResult<Option<Vec<(Member, PatId)>>> {
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
    ) -> TcResult<Option<Vec<(Member, PatId)>>> {
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
    ) -> TcResult<Option<Vec<(Member, PatId)>>> {
        let TermValidation { simplified_term_id, term_ty_id } =
            self.validator().validate_term(term_id)?;

        let reader = self.reader();

        // we need to erase  `...` here for tuples and constructors
        let captured_member = match reader.get_pat(pat_id) {
            Pat::Tuple(members) => {
                self.maybe_erase_spread_pat_from_tuple(pat_id, members, term_id)?
            }
            Pat::Constructor(constructor) => self.maybe_erase_spread_pat_from_constructor(
                pat_id,
                constructor,
                simplified_term_id,
            )?,
            _ => None,
        };

        // re-read the pattern since it may of been modified
        let pat = reader.get_pat(pat_id);
        let pat_ty = self.typer().infer_ty_of_pat(pat_id)?;

        let _ = self.unifier().unify_terms(pat_ty, term_ty_id)?;

        let mut bound_members = match pat {
            // Binding: Add the binding as a member
            Pat::Binding(binding) => Ok(Some(vec![(
                Member::variable(binding.name, binding.mutability, term_ty_id, simplified_term_id),
                pat_id,
            )])),

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
            Pat::Constructor(constructor) => {
                self.match_constructor_pat_with_term(pat_id, constructor, simplified_term_id)
            }
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
        self.match_pat_with_term_and_extract_binds(pat_id, term_id)
            .map(|members| members.map(|inner| inner.into_iter().map(|(m, _)| m).collect()))
    }
}
