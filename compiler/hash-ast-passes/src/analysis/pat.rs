use hash_ast::ast::{AstNodes, Pattern, TuplePatternEntry};

use crate::visitor::SemanticAnalysisContext;

use super::{
    error::{AnalysisErrorKind, PatternOrigin},
    SemanticAnalyser,
};

impl SemanticAnalyser {
    pub(crate) fn check_compound_pattern_rules(
        &mut self,
        ctx: &SemanticAnalysisContext,
        fields: &AstNodes<TuplePatternEntry>,
        origin: PatternOrigin,
    ) {
        let mut seen_spread_pattern = false;
        let mut seen_named_field = false;

        // Verify that no spread patterns are present in the top level
        for field in fields.iter() {
            let TuplePatternEntry { name, pattern } = field.body();

            let is_spread_pattern = matches!(pattern.body(), Pattern::Spread(_));

            // Detect an incorrect ordering of named-un/named arguments within the pattern
            if !is_spread_pattern {
                if name.is_some() {
                    seen_named_field = true;
                } else if seen_named_field {
                    self.append_error(
                        AnalysisErrorKind::AmbiguousPatternFieldOrder { origin },
                        field.span(),
                        ctx.source_id,
                    );
                }
            }

            // We only care if this is a binding-free pattern entry, and we don't
            // care where the pattern occurs if it is after or before the named/un-named
            // argument order.
            if name.is_none() && is_spread_pattern {
                if seen_spread_pattern {
                    self.append_error(
                        AnalysisErrorKind::MultipleSpreadPatterns {
                            origin: PatternOrigin::Constructor,
                        },
                        field.span(),
                        ctx.source_id,
                    );
                }

                seen_spread_pattern = true;
            }
        }
    }

    /// Here we need to check that the list pattern only contains a single spread pattern since
    /// it wouldn't make sense for there to be multiple spread patterns. This is primarily because
    /// having multiple spreads would introduce ambiguity about which elements are captured by the spread.
    /// For example in the following pattern:
    /// ```ignore
    /// >>> [..., ...x]
    /// ```
    ///
    /// Note: this isn't the only case that is erroneous, in general any list pattern with multiple
    /// spread patterns is considered to be incorrect.
    ///
    /// Which parts does the `x` spread pattern capture? It's clear that this is ambiguous and should
    /// be disallowed within the list patten.
    pub(crate) fn check_list_pattern(
        &mut self,
        ctx: &SemanticAnalysisContext,
        fields: &AstNodes<Pattern>,
    ) {
        // @@TODO: Rather than use a boolean, we should use a reference to the pattern
        //         so that we can report an auxiliary span of where the initial use of the
        //         pattern occurs.
        let mut seen_spread_pattern = false;

        for field in fields.iter() {
            if matches!(field.body(), Pattern::Spread(_)) {
                if seen_spread_pattern {
                    self.append_error(
                        AnalysisErrorKind::MultipleSpreadPatterns {
                            origin: PatternOrigin::List,
                        },
                        field.span(),
                        ctx.source_id,
                    );
                } else {
                    seen_spread_pattern = true;
                }
            }
        }
    }
}
