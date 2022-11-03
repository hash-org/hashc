use hash_types::new::stores::Stores;

use super::ctx::Context;

/// The typed semantic analysis environment.
///
/// Contains access to stores which contain the typed semantic analysis data.
/// Also has access to the context, which contains information about the
/// current scope of variables and facts.
#[derive(Debug)]
pub struct Env {
    stores: Stores,
    context: Context,
}

pub trait AccessToEnv {
    fn env(&self) -> &Env;

    fn stores(&self) -> &Stores {
        &self.env().stores
    }

    fn ctx(&self) -> &Context {
        &self.env().context
    }
}

impl Env {
    pub fn new() -> Self {
        Self { stores: Stores::new(), context: Context::new() }
    }
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

impl AccessToEnv for Env {
    fn env(&self) -> &Env {
        self
    }
}
