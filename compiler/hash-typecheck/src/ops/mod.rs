//! Contains implementations of the main operations that the typechecker should
//! be able to perform.
//!
//! Code from this module is to be used while traversing and typing the AST, in
//! order to unify types and ensure correctness.
pub mod building;
pub mod cache;
pub mod core;
pub mod discover;
pub mod exhaustiveness;
pub mod oracle;
pub mod params;
pub mod pats;
pub mod reader;
pub mod scope;
pub mod simplify;
pub mod substitute;
pub mod typing;
pub mod unify;
pub mod validate;

use self::{
    building::PrimitiveBuilder, cache::CacheManager, core::CoreDefReader, discover::Discoverer,
    exhaustiveness::ExhaustivenessChecker, oracle::Oracle, pats::PatMatcher,
    reader::PrimitiveReader, scope::ScopeManager, simplify::Simplifier, substitute::Substituter,
    typing::Typer, unify::Unifier, validate::Validator,
};
use crate::storage::{scope::ScopeId, AccessToStorage, AccessToStorageMut};

/// Trait to access various structures that can perform typechecking queries,
/// by a reference to a [StorageRef](crate::storage::StorageRef).
pub trait AccessToOps: AccessToStorage {
    /// Create an instance of [PrimitiveReader].
    fn reader(&self) -> PrimitiveReader {
        PrimitiveReader::new(self.global_storage())
    }

    /// Create an instance of an [Oracle]
    fn oracle(&self) -> Oracle {
        Oracle::new(self.storages())
    }

    /// Create an instance of [PrimitiveBuilder] from the global storage.
    fn builder(&self) -> PrimitiveBuilder {
        PrimitiveBuilder::new(self.global_storage())
    }

    /// Create an instance of [PrimitiveBuilder] from the global storage, with
    /// the given scope.
    ///
    /// See [PrimitiveBuilder] docs for more information.
    fn builder_with_scope(&self, scope: ScopeId) -> PrimitiveBuilder {
        PrimitiveBuilder::new_with_scope(self.global_storage(), scope)
    }
}

impl<T: AccessToStorage> AccessToOps for T {}

/// Trait to access various structures that can perform typechecking operations,
/// by a reference to a [StorageRefMut](crate::storage::StorageRefMut).
pub trait AccessToOpsMut: AccessToStorageMut {
    /// Create an instance of [CacheManager].
    fn cacher(&mut self) -> CacheManager {
        CacheManager::new(self.storages_mut())
    }

    /// Create an instance of [Unifier].
    fn unifier(&mut self) -> Unifier {
        Unifier::new(self.storages_mut())
    }

    /// Create an instance of [Substituter].
    fn substituter(&mut self) -> Substituter {
        Substituter::new(self.storages_mut())
    }

    /// Create an instance of [Typer].
    fn typer(&mut self) -> Typer {
        Typer::new(self.storages_mut())
    }

    /// Create an instance of [Simplifier].
    fn simplifier(&mut self) -> Simplifier {
        Simplifier::new(self.storages_mut())
    }

    /// Create an instance of [Validator].
    fn validator(&mut self) -> Validator {
        Validator::new(self.storages_mut())
    }

    /// Create an instance of [ScopeManager].
    fn scope_manager(&mut self) -> ScopeManager {
        ScopeManager::new(self.storages_mut())
    }

    /// Create an instance of [PatMatcher].
    fn pat_matcher(&mut self) -> PatMatcher {
        PatMatcher::new(self.storages_mut())
    }

    /// Create an instance of [ExhaustivenessChecker].
    fn exhaustiveness_checker(&mut self) -> ExhaustivenessChecker {
        ExhaustivenessChecker::new(self.storages_mut())
    }

    /// Create an instance of [Discoverer].
    fn discoverer(&mut self) -> Discoverer {
        Discoverer::new(self.storages_mut())
    }

    /// Create an instance of [CoreDefReader].
    fn core_defs(&mut self) -> CoreDefReader {
        CoreDefReader::new(self.storages_mut())
    }
}

impl<T: AccessToStorageMut> AccessToOpsMut for T {}
