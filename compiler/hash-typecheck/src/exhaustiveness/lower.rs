//! Lowering utilities from a [Pat] into a [DeconstructedPat] and
//! vice versa.
use std::iter::once;

use hash_utils::store::Store;
use if_chain::if_chain;
use itertools::Itertools;
use smallvec::SmallVec;

use super::{
    constant::Constant,
    construct::DeconstructedCtor,
    deconstruct::DeconstructedPat,
    fields::Fields,
    list::{List, ListKind},
    range::IntRange,
    AccessToUsefulnessOps,
};
use crate::{
    diagnostics::macros::tc_panic,
    ops::AccessToOps,
    storage::{
        deconstructed::DeconstructedPatId,
        pats::{PatArgsId, PatId},
        primitives::{
            ConstructorPat, IfPat, Level0Term, Level1Term, ListPat, LitTerm, ModDef, ModPat,
            NominalDef, Pat, PatArg, ScopeKind, SpreadPat, StructFields, Term, TupleTy,
        },
        terms::TermId,
        AccessToStorage, StorageRef,
    },
};

/// Representation of a field within a collection of patterns.
#[derive(Debug, Clone)]
pub struct FieldPat {
    /// Relative to the associated definition
    pub(crate) index: usize,
    /// Pattern associated with this field
    pub(crate) pat: PatId,
}

pub struct LowerPatOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for LowerPatOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> LowerPatOps<'tc> {
    /// Create a new [LowerPatOps].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Convert a [Pat] into a [DeconstructedPat].
    pub(crate) fn deconstruct_pat(&self, ty: TermId, pat_id: PatId) -> DeconstructedPat {
        let reader = self.reader();
        let pat = reader.get_pat(pat_id);

        let (ctor, fields) = match pat {
            Pat::Wild | Pat::Binding(_) | Pat::Spread(_) => (DeconstructedCtor::Wildcard, vec![]),

            // For all members in the scope, fill it in as a wildcard, and then provide
            // deconstructed patterns for the actual members that are specified in the
            // pattern...
            //
            // @@Speed: Could we just care about the specified fields and assume that the
            // rest are wildcards, since this seems to be redundant, might need to introduce
            // some kind of special fields that doesn't care about all of the filled in fields...
            Pat::Mod(ModPat { members }) => {
                let specified_members = reader.get_pat_args_owned(members).clone();

                let scope = match reader.get_term(ty) {
                    Term::Level1(Level1Term::ModDef(id)) => {
                        let ModDef { members, .. } = reader.get_mod_def(id);
                        let scope = self.scope_store().get(members);

                        // We should be in a constant scope
                        assert!(scope.kind == ScopeKind::Constant);
                        scope
                    }
                    _ => tc_panic!(
                        ty,
                        self,
                        "expected a module definition when deconstructing pattern!"
                    ),
                };

                let mut scope_members = scope
                    .members
                    .iter()
                    .map(|member| self.deconstruct_pat_ops().wildcard(member.ty()))
                    .collect_vec();

                // Iterate over the specified members and set the `actual` pattern here
                for member in specified_members.positional() {
                    let index = *scope.member_names.get(&member.name.unwrap()).unwrap();

                    scope_members[index] =
                        self.deconstruct_pat(scope_members[index].ty, member.pat);
                }

                (DeconstructedCtor::Single, scope_members)
            }
            // This is essentially a simplification to some unit nominal definition like
            // for example `None`..., here we need to be able to get the `type` of the
            // actual pattern in order to figure out which
            Pat::Access(_) | Pat::Const(_) => {
                // @@EnumToUnion: when enums aren't a thing, do this with a union and create a
                // `DeconstructedCtor::Variant(idx)` where `idx` is the union member number
                unreachable!()
            }
            Pat::Range(_) => todo!(),
            Pat::Lit(term) => match reader.get_term(term) {
                Term::Level0(Level0Term::Lit(lit)) => match lit {
                    LitTerm::Str(value) => (DeconstructedCtor::Str(value), vec![]),
                    LitTerm::Int { value, kind } => {
                        let value = Constant::from_int(value, kind, term);
                        let range = self.int_range_ops().range_from_constant(value);
                        (DeconstructedCtor::IntRange(range), vec![])
                    }
                    LitTerm::Char(value) => {
                        let value = Constant::from_char(value, term);
                        let range = self.int_range_ops().range_from_constant(value);
                        (DeconstructedCtor::IntRange(range), vec![])
                    }
                },
                _ => tc_panic!(term, self, "Not a constant!"),
            },
            Pat::Tuple(args) => {
                let fields = self.pat_lowerer().deconstruct_pat_fields(args);

                // We need to read the tuple type from the ctx type and then create
                // wildcard fields for all of the inner types
                match reader.get_term(ty) {
                    Term::Level1(Level1Term::Tuple(TupleTy { members })) => {
                        let members = reader.get_params_owned(members).clone();

                        // Create wild-cards for all of the tuple inner members
                        let mut wilds: SmallVec<[_; 2]> = members
                            .positional()
                            .iter()
                            .map(|member| self.deconstruct_pat_ops().wildcard(member.ty))
                            .collect();

                        // For each provided field, we want to recurse and lower the pattern further
                        for field in fields {
                            wilds[field.index] =
                                self.deconstruct_pat(wilds[field.index].ty, field.pat);
                        }

                        (DeconstructedCtor::Single, wilds.to_vec())
                    }
                    _ => tc_panic!(
                        ty,
                        self,
                        "Unexpected ty `{}` when deconstructing pattern {:?}",
                        self.for_fmt(ty),
                        pat
                    ),
                }
            }
            Pat::Constructor(ConstructorPat { args, .. }) => {
                match reader.get_term(ty) {
                    Term::Level1(Level1Term::NominalDef(nominal_def)) => {
                        let fields = self.pat_lowerer().deconstruct_pat_fields(args);

                        let (ctor, members) = match reader.get_nominal_def(nominal_def) {
                            NominalDef::Struct(struct_def) => match struct_def.fields {
                                StructFields::Explicit(members) => {
                                    (DeconstructedCtor::Single, members)
                                }
                                StructFields::Opaque => {
                                    panic!("got unexpected opaque struct-def here")
                                }
                            },
                            // @@EnumToUnion: when enums aren't a thing, do this with a union
                            NominalDef::Enum(_) => unreachable!(),
                        };

                        let args = reader.get_params_owned(members);
                        let tys = args.positional().iter().map(|param| param.ty);

                        let mut wilds: SmallVec<[_; 2]> =
                            tys.map(|ty| self.deconstruct_pat_ops().wildcard(ty)).collect();

                        // For each provided field, we want to recurse and lower the pattern further
                        for field in fields {
                            wilds[field.index] =
                                self.deconstruct_pat(wilds[field.index].ty, field.pat);
                        }

                        (ctor, wilds.to_vec())
                    }
                    _ => tc_panic!(
                        ty,
                        self,
                        "Unexpected ty `{}` when deconstructing pattern {:?}",
                        self.for_fmt(ty),
                        pat
                    ),
                }
            }
            Pat::List(ListPat { inner, .. }) => {
                let mut prefix = vec![];
                let mut suffix = vec![];
                let mut spread = false;

                let pats = reader.get_pat_args_owned(inner);
                let inner_ty = self.oracle().term_as_list_ty(ty).unwrap();

                // We don't care about the `name` of the arg because the list
                // never has the `name` assigned to anything...
                for PatArg { pat: id, .. } in pats.positional() {
                    let pat = reader.get_pat(*id);

                    if matches!(pat, Pat::Spread(_)) {
                        if spread {
                            tc_panic!(id, self, "found multiple spread patterns within list");
                        }

                        spread = true;
                    } else {
                        match spread {
                            true => suffix.push(self.deconstruct_pat(inner_ty, *id)),
                            false => prefix.push(self.deconstruct_pat(inner_ty, *id)),
                        }
                    }
                }

                // If we saw a `...` then we can't be sure of the list length and
                // so it is now considered to be variable length
                let kind = if spread {
                    ListKind::Var(prefix.len(), suffix.len())
                } else {
                    ListKind::Fixed(prefix.len() + suffix.len())
                };

                let ctor = DeconstructedCtor::List(List::new(kind));
                let fields = prefix.into_iter().chain(suffix).collect_vec();

                (ctor, fields)
            }
            Pat::Or(_) => {
                // here, we need to expand the or pattern, so that all of the
                // children patterns of the `or` become fields of the
                // deconstructed  pat.
                let pats = self.pat_lowerer().flatten_or_pat(pat_id);

                // @@Correctness: does it make sense to pass in this `ctx` since the
                // type is the type of the `or` pattern and not each pat itself, but also
                // it should be that the union-ty is simplified into a single term?
                let fields = pats.iter().map(|pat| self.deconstruct_pat(ty, *pat)).collect_vec();

                (DeconstructedCtor::Or, fields)
            }
            Pat::If(IfPat { pat, .. }) => {
                let pat = self.deconstruct_pat(ty, pat);
                pat.has_guard.set(true);

                return pat;
            }
        };

        let ctor = self.constructor_store().create(ctor);

        // Now we need to put them in the store...
        let fields = Fields::from_iter(
            fields.into_iter().map(|field| self.deconstructed_pat_store().create(field)),
        );

        DeconstructedPat::new(ctor, fields, ty, Some(pat_id))
    }

    // Convert a [DeconstructedPat] into a [Pat].
    pub(crate) fn construct_pat(&self, pat: DeconstructedPatId) -> PatId {
        let reader = self.reader();
        let pat = reader.get_deconstructed_pat(pat);

        // Short-circuit, if the pattern already has an associated `PatId`...
        if pat.id.is_some() {
            return pat.id.unwrap();
        }

        let ctor = reader.get_deconstructed_ctor(pat.ctor);

        // Build the pattern based from the constructor and the fields...
        let pat = match ctor {
            DeconstructedCtor::Single | DeconstructedCtor::Variant(_) => {
                let reader = self.reader();

                match reader.get_term(pat.ty) {
                    Term::Level1(Level1Term::Tuple(_)) => {
                        let _children = pat
                            .fields
                            .iter_patterns()
                            .map(|p| self.construct_pat(*p))
                            .collect_vec();

                        // @@Todo: immutable builder required.

                        // let args = self.builder().create_pat_args(children);
                        // Pat::Tuple(args)

                        todo!()
                    }
                    Term::Level1(Level1Term::NominalDef(_)) => {
                        let _children = pat.fields.iter_patterns().map(|p| self.construct_pat(*p));

                        // @@Todo: immutable builder required.

                        // let args = self.builder().create_pat_args(children);
                        // Pat::Constructor(ConstructorPat { subject: pat.ty, args })
                        todo!()
                    }
                    _ => tc_panic!(
                        pat.ty,
                        self,
                        "Unexpected ty `{}` when converting to pattern",
                        self.for_fmt(pat.ty),
                    ),
                }
            }
            DeconstructedCtor::IntRange(range) => self.construct_pat_from_range(pat.ty, range),
            DeconstructedCtor::Str(_) => Pat::Lit(pat.ty),
            DeconstructedCtor::List(List { kind }) => {
                let children = pat.fields.iter_patterns().map(|p| self.construct_pat(*p));

                match kind {
                    ListKind::Fixed(_) => {
                        let _inner_term = self.oracle().term_as_list_ty(pat.ty).unwrap();

                        // @@Todo: immutable builder required.

                        // let inner = self.builder().create_pat_args(children);
                        // Pat::List(ListPat { term: inner_term, inner })
                        todo!()
                    }
                    #[allow(clippy::needless_collect)]
                    ListKind::Var(prefix, _) => {
                        let mut children = children.into_iter().peekable();

                        // build the prefix and suffix components
                        let prefix: Vec<_> = children.by_ref().take(prefix).collect();
                        let suffix: Vec<_> = children.collect();

                        // Create the `spread` dummy pattern
                        let dummy = Pat::Spread(SpreadPat { name: None });
                        let spread = self.pat_store().create(dummy);

                        // Now create an inner collection of patterns with the inserted
                        // spread pattern
                        let _inner = prefix.into_iter().chain(once(spread)).chain(suffix);
                        let _term = self.oracle().term_as_list_ty(pat.ty).unwrap();

                        // @@Todo: immutable builder required.

                        // let elements = self.builder().create_pat_args(inner);
                        // Pat::List(ListPat { term, inner: elements })
                        todo!()
                    }
                }
            }
            DeconstructedCtor::Wildcard | DeconstructedCtor::NonExhaustive => Pat::Wild,
            DeconstructedCtor::Or => {
                panic!("cannot convert an `or` deconstructed pat back into pat")
            }
            DeconstructedCtor::Missing => panic!(
                "trying to convert a `Missing` constructor into a `Pat`; this is probably a bug, `Missing` should have been processed in `apply_constructors`"
            ),
        };

        // Now put the pat on the store and return it
        self.pat_store().create(pat)
    }

    /// Convert [IntRange] into a [Pat] by judging the given
    /// type that is stored within the parent [DeconstructedPat].
    pub fn construct_pat_from_range(&self, ty: TermId, range: IntRange) -> Pat {
        let (lo, hi) = range.boundaries();
        let bias = range.bias;
        let (lo, hi) = (lo ^ bias, hi ^ bias);

        if lo == hi {
            Pat::Lit(ty)
        } else {
            panic!("Ranges are not supported yet")
        }
    }

    /// Expand an `or` pattern into a passed [Vec], whilst also
    /// applying the same operation on children patterns.
    fn expand(&self, id: PatId, vec: &mut Vec<PatId>) {
        let reader = self.reader();
        let pat = reader.get_pat(id);

        if let Pat::Or(pats) = pat {
            for inner_pat in pats {
                self.expand(inner_pat, vec);
            }
        } else {
            vec.push(id)
        }
    }

    /// Internal use for expanding an [Pat::Or] into children
    /// patterns. This will also expand any children that are `or`
    /// patterns.
    pub fn flatten_or_pat(&self, pat: PatId) -> Vec<PatId> {
        let mut pats = Vec::new();
        self.expand(pat, &mut pats);

        pats
    }

    /// Function to lower a collection of pattern fields. This is used for
    /// tuple and constructor patterns. This function takes account of whether
    /// fields are named or not, and properly computes the `index` of each
    /// field based on the definition position and whether or not it is a
    /// named argument.
    pub fn deconstruct_pat_fields(&self, fields: PatArgsId) -> Vec<FieldPat> {
        let reader = self.reader();
        let args = reader.get_pat_args_owned(fields).clone();

        let pats = args
            .positional()
            .iter()
            .enumerate()
            // This tries to resolve the `index` of the argument that is being passed
            // within the tuple field. If the tuple has named arguments, then we have
            // to use the parameter list in order to resolve the index. By now it should be
            // verified that no un-named arguments appear after named arguments as this
            // creates an ambiguous ordering of arguments.
            .map(|(index, arg)| -> FieldPat {
                let field = if_chain! {
                    if let Some(name) = arg.name;
                    if let Some((arg_index, _)) = args.get_by_name(name);
                    then {
                        arg_index
                    } else {
                        index
                    }
                };

                FieldPat { index: field, pat: arg.pat }
            })
            .collect_vec();

        pats
    }
}
