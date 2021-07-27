use hash_alloc::Castle;
use lazy_static::lazy_static;

lazy_static! {
    pub static ref STATIC_CASTLE: Castle = Castle::new();
}
