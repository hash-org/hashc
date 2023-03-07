//! This deals with lowering declarations,assigning them to a [Local],
//! and later resolving references to the locals with the current [Builder].

use hash_ir::{
    ir::{BasicBlock, Local, LocalDecl, Place},
    ty::{IrTyId, Mutability},
};
use hash_reporting::macros::panic_on_span;
use hash_source::location::Span;
use hash_tir::{
    arrays::ArrayPat,
    control::{IfPat, OrPat},
    data::CtorPat,
    environment::env::AccessToEnv,
    pats::{Pat, PatId},
    scopes::{BindingPat, DeclTerm},
    symbols::Symbol,
    terms::TermId,
    tuples::TuplePat,
    utils::common::CommonUtils,
};
use hash_utils::store::{CloneStore, SequenceStore};

use super::{candidate::Candidate, BlockAnd, Builder};
use crate::build::{place::PlaceBuilder, unpack, BlockAndExtend, LocalKey};

impl<'tcx> Builder<'tcx> {
    /// Push a [LocalDecl] in the current [Builder] with the associated
    /// [LocalKey]. This will put the [LocalDecl] into the declarations, and
    /// create an entry in the lookup map so that the [Local] can be looked up
    /// via the name of the local and the scope that it is in.
    pub(crate) fn push_local(&mut self, decl: LocalDecl, key: LocalKey) -> Local {
        let is_named = decl.name.is_some();
        let index = self.declarations.push(decl);

        // If the declaration has a name i.e. not an auxiliary local, then
        // we can push it into the `declaration_map`.
        if is_named {
            self.declaration_map.insert(key, index);
        }

        index
    }

    /// This function handles the lowering of an declaration term.
    pub(crate) fn lower_declaration(
        &mut self,
        mut block: BasicBlock,
        decl: &DeclTerm,
        decl_span: Span,
    ) -> BlockAnd<()> {
        if let Some(value) = &decl.value {
            // First, we declare all of the bindings that are present
            // in the pattern, and then we place the expression into
            // the pattern using `expr_into_pat`.
            self.declare_bindings(decl.bind_pat);

            unpack!(block = self.tir_term_into_pat(block, decl.bind_pat, *value));
        } else {
            panic_on_span!(
                decl_span.into_location(self.source_id),
                self.source_map(),
                "expected initialisation value, declaration are expected to have values (for now)."
            );
        };

        // if the declaration has an initialiser, then we need to deal with
        // the initialisation block.
        block.unit()
    }

    /// Declare all of the bindings that are present in the left-most variant
    /// of the pattern. This is guaranteed to cover all bindings that can be
    /// bound within the pattern since we have already checked that all pattern
    /// variants declare the same binds of the same type, on the same
    /// pattern level.
    pub(super) fn declare_bindings(&mut self, pat: PatId) {
        self.visit_primary_pattern_bindings(pat, &mut |this, mutability, name, _span, ty| {
            let key = this.local_key_from_symbol(name);
            let name = this.symbol_name(name);
            let local = LocalDecl::new(name, mutability, ty);
            this.push_local(local, key);
        })
    }

    fn visit_primary_pattern_bindings(
        &mut self,
        pat_id: PatId,
        f: &mut impl FnMut(&mut Self, Mutability, Symbol, Span, IrTyId),
    ) {
        let span = self.span_of_pat(pat_id);
        let pat = self.stores().pat().get(pat_id);

        match pat {
            Pat::Binding(BindingPat { name, is_mutable, .. }) => {
                let binding = self.get_symbol(name).name;

                // If the symbol has no associated name, then it is not binding
                // anything...
                if binding.is_none() {
                    return;
                }

                // @@Todo: when we support `k @ ...` patterns, we need to know
                // when this is a primary pattern or not.

                let ty = self.ty_id_from_tir_pat(pat_id);
                let mutability =
                    if is_mutable { Mutability::Mutable } else { Mutability::Immutable };

                f(self, mutability, name, span, ty);
            }
            Pat::Ctor(CtorPat { ctor_pat_args: fields, ctor_pat_args_spread: spread, .. })
            | Pat::Tuple(TuplePat { data: fields, data_spread: spread }) => {
                self.stores().pat_args().get_vec(fields).iter().for_each(|field| {
                    self.visit_primary_pattern_bindings(field.pat.assert_pat(), f);
                });

                if let Some(spread_pat) = spread && spread_pat.stack_member.is_some() {
                        //@@Todo: we need to get the type of the spread.
                        let ty = self.ty_id_from_tir_pat(pat_id);

                        f(
                            self,
                            // @@Todo: it should be possible to make this a mutable
                            // pattern reference, for now we assume it is always immutable.
                            Mutability::Immutable,
                            spread_pat.name,
                            span,
                            ty
                        )
                    }
            }
            Pat::Array(ArrayPat { pats, spread }) => {
                if let Some(spread_pat) = spread && spread_pat.stack_member.is_some() {
                    let index = spread_pat.index;

                    // Create the fields into an iterator, and only take the `prefix`
                    // amount of fields to iterate
                    let pats = self.stores().pat_list().get_vec(pats);

                        let prefix_fields = pats.iter().take(index);
                        for field in prefix_fields {
                            self.visit_primary_pattern_bindings(field.assert_pat(), f);
                        }

                        //@@TodoTIR: we need to get the type of the spread.
                        let ty = self.ty_id_from_tir_pat(pat_id);

                        f(
                            self,
                            // @@Todo: it should be possible to make this a mutable
                            // pattern reference, for now we assume it is always immutable.
                            Mutability::Immutable,
                            spread_pat.name,
                            span,
                            ty
                        );

                        // Now deal with the suffix fields.
                        let suffix_fields = pats.iter().skip(index);

                        for field in suffix_fields {
                            self.visit_primary_pattern_bindings(field.assert_pat(), f);
                        }
                } else {
                    self.stores().pat_list().get_vec(pats).iter()
                        .for_each(|pat| {
                            self.visit_primary_pattern_bindings(pat.assert_pat(), f);
                        });
                }
            }
            Pat::Or(OrPat { alternatives }) => {
                // We only need to visit the first variant since we already
                // check that the variant bindings are all the same.
                if let Some(pat) = self.stores().pat_list().try_get_at_index(alternatives, 0) {
                    self.visit_primary_pattern_bindings(pat.assert_pat(), f);
                }
            }
            Pat::If(IfPat { pat, .. }) => {
                self.visit_primary_pattern_bindings(pat, f);
            }
            // These patterns never have any bindings.
            Pat::Range(_) | Pat::Lit(_) => {}
        }
    }

    /// Lower a given [Term] into the provided [Pat]. It is expected
    /// that the pattern is irrefutable, since this is verified during
    /// typechecking via exhaustiveness.
    fn tir_term_into_pat(
        &mut self,
        mut block: BasicBlock,
        pat_id: PatId,
        term: TermId,
    ) -> BlockAnd<()> {
        let pat = self.stores().pat().get(pat_id);

        let mut place_into_pat = |this: &mut Self| {
            let place_builder =
                unpack!(block = this.as_place_builder(block, term, Mutability::Mutable));
            this.place_into_pat(block, pat_id, place_builder)
        };

        match pat {
            Pat::Binding(BindingPat { name, .. }) => {
                // we lookup the local from the current scope, and get the place of where
                // to place this value.
                if let Some(local) = self.lookup_local_symbol(name) {
                    let place = Place::from_local(local, self.ctx);

                    unpack!(block = self.term_into_dest(place, block, term));
                    block.unit()
                } else {
                    // If the bind has no local, this must be a wildcard
                    place_into_pat(self)
                }
            }
            // The long path, we go through creating candidates and then
            // automatically building places for each candidate, etc.
            _ => place_into_pat(self),
        }
    }

    /// Construct a [Candidate] for a given [ast::Pat], and then lower
    /// the pattern with a single candidate, and the expression that
    /// is the initialising value of the patterns.
    fn place_into_pat(
        &mut self,
        block: BasicBlock,
        pat: PatId,
        place: PlaceBuilder,
    ) -> BlockAnd<()> {
        let pat_span = self.span_of_pat(pat);

        let mut candidate = Candidate::new(pat_span, pat, &place, false);
        self.lower_match_tree(block, pat_span, pat_span, &mut [&mut candidate]);

        self.bind_pat(pat_span, pat, candidate).unit()
    }
}
