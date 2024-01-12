//! Functions to perform pattern matching between terms and patterns. This is
//! used for normalisation.
// @@Improvement: perhaps the contents of this module should be reorganised into
// traits similar to `Operations` which allow a node `X` to be matched against a
// pattern `P`.
use hash_ast::ast::RangeEnd;
use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    intrinsics::utils::is_true_bool_ctor,
    tir::{
        ArrayTerm, Lit, LitPat, NodeId, NodesId, Pat, PatId, PatOrCapture, RangePat, Spread,
        SymbolId, Term, TermId,
    },
};

use crate::{env::TcEnv, options::normalisation::NormaliseSignal, tc::Tc};

/// The result of matching a pattern against a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatchResult {
    /// The pattern matched successfully.
    Successful,
    /// The pattern failed to match.
    Failed,
    /// The term could not be normalised enough to be matched.
    Stuck,
}

impl<E: TcEnv> Tc<'_, E> {
    /// Match the given arguments with the given pattern arguments.
    ///
    /// Also takes into account the spread.
    ///
    /// If the pattern arguments match, the given closure is called with the
    /// bindings.
    pub fn match_some_sequence_and_get_binds(
        &self,
        length: usize,
        spread: Option<Spread>,
        extract_spread_list: impl Fn(Spread) -> TermId,
        get_ith_pat: impl Fn(usize) -> PatOrCapture,
        get_ith_term: impl Fn(usize) -> TermId,
        f: &mut impl FnMut(SymbolId, TermId),
    ) -> Result<MatchResult, NormaliseSignal> {
        // We assume that the term list is well-typed with respect to the pattern list.

        let mut element_i = 0;
        while element_i < length {
            let arg_i = get_ith_term(element_i);
            let pat_arg_i = get_ith_pat(element_i);

            match pat_arg_i {
                PatOrCapture::Pat(pat_id) => {
                    match self.match_value_and_get_binds(arg_i, pat_id, f)? {
                        MatchResult::Successful => {
                            // Continue
                        }
                        MatchResult::Failed => {
                            // The match failed
                            return Ok(MatchResult::Failed);
                        }
                        MatchResult::Stuck => {
                            // The match is stuck
                            return Ok(MatchResult::Stuck);
                        }
                    }
                }
                PatOrCapture::Capture(_) => {
                    // Handled below
                }
            }

            element_i += 1;
        }

        // Capture the spread
        if let Some(spread) = spread {
            let spread_list = extract_spread_list(spread);
            f(spread.name, spread_list);
        }

        Ok(MatchResult::Successful)
    }

    /// Match the given value with the given pattern, running `f` every time a
    /// bind is discovered.
    ///
    /// The term must be normalised and well-typed with respect to the pattern.
    pub fn match_value_and_get_binds(
        &self,
        term_id: TermId,
        pat_id: PatId,
        f: &mut impl FnMut(SymbolId, TermId),
    ) -> Result<MatchResult, NormaliseSignal> {
        let evaluated_id = self.normalise_node(term_id)?;
        let evaluated = *evaluated_id.value();
        match (evaluated, *pat_id.value()) {
            (_, Pat::Or(pats)) => {
                // Try each alternative in turn:
                for pat in pats.alternatives.iter() {
                    // First collect the bindings locally

                    match self.match_value_and_get_binds(term_id, pat.assert_pat(), f)? {
                        MatchResult::Successful => {
                            return Ok(MatchResult::Successful);
                        }
                        MatchResult::Failed => {
                            // Try the next alternative
                            continue;
                        }
                        MatchResult::Stuck => {
                            return Ok(MatchResult::Stuck);
                        }
                    }
                }
                Ok(MatchResult::Failed)
            }

            (_, Pat::If(if_pat)) => {
                if let MatchResult::Successful =
                    self.match_value_and_get_binds(term_id, if_pat.pat, f)?
                {
                    // Check the condition:
                    let cond = self.normalise_node_fully(if_pat.condition)?;
                    if is_true_bool_ctor(cond) {
                        return Ok(MatchResult::Successful);
                    }
                }

                Ok(MatchResult::Failed)
            }

            // Bindings, always successful
            (_, Pat::Binding(binding)) => {
                f(binding.name, evaluated_id);
                Ok(MatchResult::Successful)
            }

            // Tuples
            (Term::Tuple(tuple_term), Pat::Tuple(tuple_pat)) => self.match_args_and_get_binds(
                tuple_term.data,
                tuple_pat.data,
                // Tuples can have spreads, which return tuples
                tuple_pat.data_spread,
                f,
            ),
            (_, Pat::Tuple(_)) => Ok(MatchResult::Stuck),

            // Constructors
            (Term::Ctor(ctor_term), Pat::Ctor(ctor_pat)) => {
                // We assume that the constructor is well-typed with respect to
                // the pattern, so that data params already match.

                if ctor_term.ctor != ctor_pat.ctor {
                    Ok(MatchResult::Failed)
                } else {
                    self.match_args_and_get_binds(
                        ctor_term.ctor_args,
                        ctor_pat.ctor_pat_args,
                        // Constructors can have spreads, which return tuples
                        ctor_pat.ctor_pat_args_spread,
                        f,
                    )
                }
            }
            (_, Pat::Ctor(_)) => Ok(MatchResult::Stuck),

            // Ranges
            (Term::Lit(lit_term), Pat::Range(RangePat { lo, hi, end })) => {
                // If we know both of the range ends, then we can simply evaluate it
                // using the value. If not, we then create the `min` or `max` values
                // that are missing based on the type of the literal.

                // Disallow open excluded ranges to be parameterless. This isn't strictly
                // necessary, but it is strange to write `..<` and mean to match
                // everything but the end. This is checked and reported as an
                // error in untyped-semantics.
                if end == RangeEnd::Excluded {
                    debug_assert!(hi.is_some())
                }

                let lo = lo.map(|LitPat(lit)| *lit.value());
                let hi = hi.map(|LitPat(lit)| *lit.value());

                Ok(match (*lit_term.value(), lo, hi) {
                    (Lit::Const(value), Some(Lit::Const(lo)), Some(Lit::Const(hi))) => {
                        self.match_literal_to_range(value, Some(lo), Some(hi), end)
                    }
                    (Lit::Const(value), Some(Lit::Const(lo)), None) => {
                        self.match_literal_to_range(value, Some(lo), None, end)
                    }
                    (Lit::Const(value), None, Some(Lit::Const(hi))) => {
                        self.match_literal_to_range(value, None, Some(hi), end)
                    }
                    _ => MatchResult::Stuck,
                })
            }
            (_, Pat::Range(_)) => Ok(MatchResult::Stuck),

            // Literals
            (Term::Lit(lit_term), Pat::Lit(lit_pat)) => {
                match (*lit_term.value(), *(*lit_pat).value()) {
                    (Lit::Const(a), Lit::Const(b)) => Ok(self.match_literal_to_literal(a, b)),
                    _ => Ok(MatchResult::Stuck),
                }
            }
            // Arrays
            (Term::Array(array_term), Pat::Array(array_pat)) => {
                // Evaluate the length of the array term.
                let Some(length) = self.normalise_array_term_len(array_term)? else {
                    return Ok(MatchResult::Stuck);
                };

                self.match_some_sequence_and_get_binds(
                    length,
                    array_pat.spread,
                    |sp| {
                        // Lists can have spreads, which return sublists
                        Term::from(
                            Term::Array(ArrayTerm::Normal(
                                self.extract_spread_list(array_term, array_pat.pats),
                            )),
                            sp.name.origin().computed(),
                        )
                    },
                    |i| array_pat.pats.elements().at(i).unwrap(),
                    |i| match array_term {
                        ArrayTerm::Normal(elements) => elements.elements().at(i).unwrap(),
                        ArrayTerm::Repeated(subject, _) => subject,
                    },
                    f,
                )
            }
            (_, Pat::Lit(_)) => Ok(MatchResult::Stuck),
            (_, Pat::Array(_)) => Ok(MatchResult::Stuck),
        }
    }
}
