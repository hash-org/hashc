use std::{
    collections::{BTreeMap, HashMap},
    slice::SliceIndex,
};

use hash_alloc::{brick::Brick, collections::row::Row, row, Wall};
use hash_utils::counter;

use crate::{
    error::TypecheckResult,
    types::{FnType, TypeId, TypeList, Types},
    unify::{Substitution, Unifier},
};

counter! {
    name: TraitId,
    counter_name: TRAIT_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug)]
pub struct TraitBounds<'c> {
    pub bounds: Row<'c, TraitBound<'c>>,
}

impl<'c> TraitBounds<'c> {
    pub fn empty() -> Self {
        Self { bounds: row![] }
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
    pub trait_id: TraitId,
    pub args: TypeList<'c>,
    pub bounds: TraitBounds<'c>,
}

impl<'c> TraitImpl<'c> {
    pub fn can_resolve(&self, fn_args: &TypeList<'c>, traits: &Traits) -> bool {
        let trt = traits.get(self.trait_id);
        todo!()

        // first, does it satisfy trait bounds?
        // trait foo = <A, B, C, ...> => (A, C, int, B, ...) => (B, D, E, str, Map<B, E>, ...)
        // let foo<Bar<X>, Car<Y>, Dar<Z>, ...> = (Bar<X>, Dar<Z>, ...) => (...)
        //
        // --- types: Bar<int>, Dar<Map<str, int>>, ...
        // foo(new_bar(x), new_dar(z), ...)

        // let unifier = Unifier::new(module_storage, global_storage)
        //     .unify(target, source, UnifyStrategy::CheckOnly)
        //     .is_ok();

        // then, does it satisfy impl bounds?

        // let substitutions = self.args.iter().zip(trt.args.iter()).
    }

    pub fn instantiate(
        &self,
        fn_type: &FnType<'c>,
        unifier: &mut Unifier,
        traits: &Traits,
        types: &mut Types<'c, '_>,
        wall: &Wall<'c>,
    ) -> TypecheckResult<Substitution> {
        let trt = traits.get(self.trait_id);

        let base_sub = Substitution::from_vars(&trt.args, types);
        let impl_sub = Substitution::from_vars(&self.args, types);

        // let base_subbed_args = 

        // let base_subbed_fn_type = base_sub.apply(trt.fn_type, types, unifier, wall);

        // let impl_and_base_subbed_impl_args = self.args.iter().map(|&a| {
        //     impl_sub
        //         .clone()
        //         .extend(&base_sub)
        //         .apply(a, types, unifier, wall)
        // });


        // let impl_subbed_fn_type = impl_sub.apply(self.fn_type, types, unifier, wall);

        todo!()
    }
}

#[derive(Debug)]
pub struct Trait<'c> {
    pub args: TypeList<'c>,
    pub bounds: TraitBounds<'c>,
    pub fn_type: TypeId,
}

#[derive(Debug)]
pub struct ImplsForTrait<'c> {
    trt: TraitId,
    impls: BTreeMap<TraitImplId, TraitImpl<'c>>,
}

impl<'c> ImplsForTrait<'c> {
    pub fn resolve_call(&self, fn_args: &[TypeId]) -> TraitImplId {
        todo!();
        // for (&impl_id, impl) in self.impls.iter() {
        // }
    }
}

#[derive(Debug)]
pub struct TraitImpls<'c, 'w> {
    data: HashMap<TraitId, ImplsForTrait<'c>>,
    wall: &'w Wall<'c>,
}

impl<'c, 'w> TraitImpls<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        Self {
            data: HashMap::new(),
            wall,
        }
    }

    pub fn for_trait(&self, trait_id: TraitId) -> &ImplsForTrait<'c> {
        self.data.get(&trait_id).unwrap()
    }

    pub fn resolve_call(trait_id: TraitId, fn_args: &[TypeId]) -> TraitImplId {
        // Should substitute given TypeIds with their correct version from the trait impl!

        todo!()
    }
}

#[derive(Debug)]
pub struct Traits<'c, 'w> {
    data: HashMap<TraitId, Brick<'c, Trait<'c>>>,
    wall: &'w Wall<'c>,
}

impl<'c, 'w> Traits<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        Self {
            data: HashMap::new(),
            wall,
        }
    }

    pub fn get(&self, trait_id: TraitId) -> &Trait<'c> {
        self.data.get(&trait_id).unwrap()
    }

    pub fn create(&mut self, trt: Trait<'c>) -> TraitId {
        let id = TraitId::new();
        self.data.insert(id, Brick::new(trt, self.wall));
        id
    }
}

#[derive(Debug)]
pub struct CoreTraits {
    pub hash: TraitId,
    pub eq: TraitId,
}

impl<'c, 'w> CoreTraits {
    pub fn create(types: &mut Types<'c, 'w>, wall: &'w Wall<'c>) -> Self {
        todo!()
    }
}
