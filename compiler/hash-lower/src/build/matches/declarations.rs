//! This deals with lowering declarations,assigning them to a [Local],
//! and later resolving references to the locals with the current [Builder].

use hash_ast::ast::AstNodeId;
use hash_ir::{
    ir::{BasicBlock, Local, LocalDecl, Place},
    ty::{IrTyId, Mutability},
};
use hash_reporting::macros::panic_on_span;
use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    scopes::{BindingPat, Decl},
    tir::{ArrayPat, CtorPat, IfPat, NodesId, OrPat, Pat, PatId, SymbolId, TermId, TuplePat},
};

use super::{candidate::Candidate, BlockAnd, BodyBuilder};
use crate::build::{place::PlaceBuilder, unpack, BlockAndExtend};

impl<'tcx> BodyBuilder<'tcx> {
    /// Push a [LocalDecl] in the current [BodyBuilder] with the associated
    /// [Symbol]. This will put the [LocalDecl] into the declarations, and
    /// create an entry in the lookup map so that the [Local] can be looked up
    /// via the name of the local and the scope that it is in.
    pub(crate) fn push_local(&mut self, key: SymbolId, decl: LocalDecl) -> Local {
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
        decl: &Decl,
        decl_origin: AstNodeId,
    ) -> BlockAnd<()> {
        if let Some(value) = &decl.value {
            // First, we declare all of the bindings that are present
            // in the pattern, and then we place the expression into
            // the pattern using `expr_into_pat`.
            self.declare_bindings(decl.bind_pat);

            unpack!(block = self.tir_term_into_pat(block, decl.bind_pat, *value));
        } else {
            panic_on_span!(
                decl_origin.span(),
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
            let local = LocalDecl::new(name.ident(), mutability, ty);
            this.push_local(name, local);
        })
    }

    fn visit_primary_pattern_bindings(
        &mut self,
        pat: PatId,
        f: &mut impl FnMut(&mut Self, Mutability, SymbolId, AstNodeId, IrTyId),
    ) {
        let span = self.span_of_pat(pat);

        match *pat.value() {
            Pat::Binding(BindingPat { name, is_mutable, .. }) => {
                // If the symbol has no associated name, then it is not binding
                // anything...
                if name.borrow().name.is_none() {
                    return;
                }

                // @@Future: when we support `k @ ...` patterns, we need to know
                // when this is a primary pattern or not.

                let ty = self.ty_id_from_tir_pat(pat);
                let mutability =
                    if is_mutable { Mutability::Mutable } else { Mutability::Immutable };

                f(self, mutability, name, span, ty);
            }
            Pat::Ctor(CtorPat { ctor_pat_args: fields, ctor_pat_args_spread: spread, .. })
            | Pat::Tuple(TuplePat { data: fields, data_spread: spread }) => {
                fields.elements().borrow().iter().for_each(|field| {
                    self.visit_primary_pattern_bindings(field.pat.assert_pat(), f);
                });

                if let Some(spread_pat) = spread {
                    //@@Todo: we need to get the type of the spread.
                    let ty = self.ty_id_from_tir_pat(pat);

                    f(
                        self,
                        // @@Todo: it should be possible to make this a mutable
                        // pattern reference, for now we assume it is always immutable.
                        Mutability::Immutable,
                        spread_pat.name,
                        span,
                        ty,
                    )
                }
            }
            Pat::Array(ArrayPat { pats, spread }) => {
                if let Some(spread_pat) = spread {
                    let index = spread_pat.index;

                    // Create the fields into an iterator, and only take the `prefix`
                    // amount of fields to iterate
                    let pats = pats.value();

                    let prefix_fields = pats.iter().take(index);
                    for field in prefix_fields {
                        self.visit_primary_pattern_bindings(field.assert_pat(), f);
                    }

                    //@@TodoTIR: we need to get the type of the spread.
                    let ty = self.ty_id_from_tir_pat(pat);

                    f(
                        self,
                        // @@Todo: it should be possible to make this a mutable
                        // pattern reference, for now we assume it is always immutable.
                        Mutability::Immutable,
                        spread_pat.name,
                        span,
                        ty,
                    );

                    // Now deal with the suffix fields.
                    let suffix_fields = pats.iter().skip(index);

                    for field in suffix_fields {
                        self.visit_primary_pattern_bindings(field.assert_pat(), f);
                    }
                } else {
                    pats.borrow().iter().for_each(|pat| {
                        self.visit_primary_pattern_bindings(pat.assert_pat(), f);
                    });
                }
            }
            Pat::Or(OrPat { alternatives }) => {
                // We only need to visit the first variant since we already
                // check that the variant bindings are all the same.
                if let Some(pat) = alternatives.at(0) {
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
        pat: PatId,
        term: TermId,
    ) -> BlockAnd<()> {
        let mut place_into_pat = |this: &mut Self| {
            let place_builder =
                unpack!(block = this.as_place_builder(block, term, Mutability::Mutable));
            this.place_into_pat(block, pat, place_builder)
        };

        match *pat.value() {
            Pat::Binding(BindingPat { name, .. }) => {
                // we lookup the local from the current scope, and get the place of where
                // to place this value.
                if let Some(local) = self.lookup_local(name) {
                    let place = Place::from_local(local);

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
