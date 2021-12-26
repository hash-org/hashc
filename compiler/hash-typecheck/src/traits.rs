use std::{
    collections::{BTreeMap, HashMap},
};

use hash_alloc::{collections::row::Row, row};
use hash_utils::counter;

use crate::types::TypeList;

counter! {
    name: TraitId,
    counter_name: TRAIT_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug)]
pub struct TraitBounds<'c> {
    data: Row<'c, TraitBound<'c>>,
}

impl<'c> TraitBounds<'c> {
    pub fn empty() -> Self {
        Self { data: row![] }
    }

    // pub fn map(&self, f: impl FnMut(&TraitBound<'c>) -> TraitBound<'c>) -> Self {
    //     TraitBounds {
    //         data: Row::from_iter(self.data.iter().map(f), &self.wall),
    //         wall: self.wall.clone(),
    //     }
    // }
}

#[derive(Debug)]
pub struct TraitBound<'c> {
    pub trt: TraitId,
    pub params: TypeList<'c>,
}

impl TraitBound<'_> {}

counter! {
    name: TraitImplId,
    counter_name: TRAIT_IMPL_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug)]
pub struct TraitImpl<'c> {
    pub args: TypeList<'c>,
    pub bounds: TraitBounds<'c>,
}

impl<'c> TraitImpl<'c> {
    pub fn instantiate(&self, given_args: &TypeList<'c>) -> Option<()> {
        if given_args.len() != self.args.len() {
            // @@TODO: error
            return None;
        }

        for (&_trait_arg, &_given_arg) in self.args.iter().zip(given_args.iter()) {}

        None
    }
}

#[derive(Debug, Default)]
pub struct Trait {}

#[derive(Debug)]
pub struct ImplsForTrait<'c> {
    trt: TraitId,
    impls: BTreeMap<TraitImplId, TraitImpl<'c>>,
}

#[derive(Debug, Default)]
pub struct TraitImpls<'c> {
    data: HashMap<TraitId, ImplsForTrait<'c>>,
}

#[derive(Debug, Default)]
pub struct Traits {
    data: HashMap<TraitId, Trait>,
}

impl Traits {
    pub fn new() -> Self {
        Self::default()
    }
}
