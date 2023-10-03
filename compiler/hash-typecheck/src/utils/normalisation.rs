//! General utilities for normalising TIR terms.
//!
//! These are generic wrapper functions around
//! `Operations::try_normalise`, for convenience.
use std::{cell::Cell, ops::ControlFlow};

use hash_storage::store::statics::SingleStoreId;
use hash_tir::visitor::{Atom, Map, Visitor};

use crate::{
    env::TcEnv,
    errors::TcResult,
    options::normalisation::{
        already_normalised, normalisation_result_control_flow_into, NormalisationMode,
        NormalisationState, NormaliseResult, NormaliseSignal,
    },
    tc::Tc,
    traits::OperationsOnNode,
};

impl<'env, T: TcEnv + 'env> Tc<'env, T> {
    /// Normalise the given atom, in-place.
    ///
    /// Returns `true` if the atom was normalised, `false` if it was already
    /// normalised.
    ///
    /// This does not emit any normalisation signals.
    pub fn normalise_node_in_place_no_signals<N>(&self, atom: N) -> TcResult<bool>
    where
        Visitor: Map<N>,
        N: SingleStoreId,
    {
        if let Some(result) = self.potentially_normalise_node_no_signals(atom)? {
            atom.set(result.value());
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Normalise the given atom, if applicable, or return `None` if already
    /// normalised.
    ///
    /// This does not emit any normalisation signals.
    pub fn potentially_normalise_node_no_signals<N>(&self, atom: N) -> TcResult<Option<N>>
    where
        Visitor: Map<N>,
    {
        match self.potentially_normalise_node(atom) {
            Ok(t) => Ok(t),
            Err(e) => match e {
                NormaliseSignal::Break | NormaliseSignal::Continue | NormaliseSignal::Return(_) => {
                    panic!("Got signal when normalising: {e:?}")
                }
                NormaliseSignal::Err(e) => Err(e),
            },
        }
    }

    /// Normalise the given atom.
    ///
    /// This does not return any normalisation signals.
    pub fn normalise_node_no_signals<N: Copy>(&self, atom: N) -> TcResult<N>
    where
        Visitor: Map<N>,
    {
        match self.normalise_node(atom) {
            Ok(t) => Ok(t),
            Err(e) => match e {
                NormaliseSignal::Break | NormaliseSignal::Continue | NormaliseSignal::Return(_) => {
                    panic!("Got signal when normalising: {e:?}")
                }
                NormaliseSignal::Err(e) => Err(e),
            },
        }
    }

    /// Normalise the given atom.
    pub fn normalise_node<N: Copy>(&self, atom: N) -> Result<N, NormaliseSignal>
    where
        Visitor: Map<N>,
    {
        match self.potentially_normalise_node(atom)? {
            Some(atom) => Ok(atom),
            None => Ok(atom),
        }
    }

    /// Same as `normalise_node`, but with a given evaluation state,
    /// recording the normalisation.
    pub fn normalise_node_and_record<N: Copy>(
        &self,
        atom: N,
        state: &NormalisationState,
    ) -> Result<N, NormaliseSignal>
    where
        Visitor: Map<N>,
    {
        match self.potentially_normalise_node(atom)? {
            Some(atom) => {
                state.set_normalised();
                Ok(atom)
            }
            None => Ok(atom),
        }
    }

    /// Normalise a node in `NormalisationMode::Full`.
    pub fn normalise_node_fully<N: Copy>(&self, atom: N) -> Result<N, NormaliseSignal>
    where
        Visitor: Map<N>,
    {
        self.normalisation_opts.mode.enter(NormalisationMode::Full, || self.normalise_node(atom))
    }

    /// Same as `normalise_node`, but only occurs if the atom is not nested or
    /// if the normalisation mode is `NormalisationMode::Full`.
    pub fn normalise_nested_node_and_record<N: Copy>(
        &self,
        atom: N,
        state: &NormalisationState,
    ) -> Result<N, NormaliseSignal>
    where
        Visitor: Map<N>,
    {
        match self.normalisation_opts.mode.get() {
            NormalisationMode::Full => self.normalise_node_and_record(atom, state),
            NormalisationMode::Weak => Ok(atom),
        }
    }

    /// Normalise the given atom, if applicable, or return `None` if already
    /// normalised.
    pub fn potentially_normalise_node<N>(&self, atom: N) -> NormaliseResult<N>
    where
        Visitor: Map<N>,
    {
        let mut traversal = self.visitor();
        traversal.set_visit_fns_once(false);

        let st = NormalisationState::new();
        let nested = Cell::new(false);
        let result = traversal.try_map(atom, |atom| -> Result<_, NormaliseSignal> {
            let old_mode = if self.normalisation_opts.mode.get() == NormalisationMode::Weak
                && self.has_effects(atom) == Some(true)
            {
                // If the atom has effects, we need to evaluate it fully
                let old = self.normalisation_opts.mode.get();
                self.normalisation_opts.mode.set(NormalisationMode::Full);
                old
            } else {
                // Otherwise, we can just evaluate it normally
                self.normalisation_opts.mode.get()
            };

            let result = match self.normalise_atom_once(atom, nested.get())? {
                Some(result @ ControlFlow::Break(_)) => {
                    st.set_normalised();
                    Ok(result)
                }
                Some(result @ ControlFlow::Continue(())) => Ok(result),
                None => Ok(ControlFlow::Break(atom)),
            };

            self.normalisation_opts.mode.set(old_mode);

            if self.normalisation_opts.mode.get() == NormalisationMode::Weak {
                nested.set(true);
            }
            result
        })?;

        if st.has_normalised() {
            Ok(Some(result))
        } else {
            Ok(None)
        }
    }

    /// Normalise an atom once, for use with `Visitor`'s `Map`.
    fn normalise_atom_once(&self, atom: Atom, nested: bool) -> NormaliseResult<ControlFlow<Atom>> {
        if nested && self.normalisation_opts.mode.get() == NormalisationMode::Weak {
            // If we're in weak mode, we don't want to evaluate nested atoms
            return already_normalised();
        }

        match atom {
            Atom::Term(term) => {
                normalisation_result_control_flow_into(self.try_normalise_node(term))
            }
            // @@Temporary: can be removed soon when FnDefIds are no longer a thing.
            Atom::FnDef(_) => already_normalised(),
            Atom::Pat(pat) => normalisation_result_control_flow_into(self.try_normalise_node(pat)),
            Atom::Lit(lit) => normalisation_result_control_flow_into(self.try_normalise_node(lit)),
        }
    }
}
