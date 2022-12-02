// @@Docs
use derive_more::Constructor;
use hash_utils::store::{CloneStore, SequenceStoreKey};

use crate::{
    impl_access_to_env,
    new::{
        environment::env::{AccessToEnv, Env},
        terms::{Term, TermId},
    },
};

#[derive(Constructor, Debug)]
pub struct Classifier<'tc> {
    env: &'tc Env<'tc>,
}

impl_access_to_env!(Classifier<'tc>);

impl<'tc> Classifier<'tc> {
    pub fn term_is_void(&self, term_id: TermId) -> bool {
        matches! {
          self.stores().term().get(term_id),
          Term::Tuple(tuple_term) if tuple_term.data.is_empty()
        }
    }
}
