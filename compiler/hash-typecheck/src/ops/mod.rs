//! Contains implementations of the main operations that the typechecker should
//! be able to perform.
//!
//! Code from this module is to be used while traversing and typing the AST, in
//! order to unify types and ensure correctness.
pub mod bootstrap;
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
use crate::{
    diagnostics::TcDiagnostics,
    storage::{scope::ScopeId, AccessToStorage},
};

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

    /// Create an instance of [CacheManager].
    fn cacher(&self) -> CacheManager {
        CacheManager::new(self.storages())
    }

    /// Create a [TcDiagnostics]
    fn diagnostics(&self) -> TcDiagnostics<Self> {
        TcDiagnostics(self)
    }

    /// Create an instance of [Unifier].
    fn unifier(&self) -> Unifier {
        Unifier::new(self.storages())
    }

    /// Create an instance of [Substituter].
    fn substituter(&self) -> Substituter {
        Substituter::new(self.storages())
    }

    /// Create an instance of [Typer].
    fn typer(&self) -> Typer {
        Typer::new(self.storages())
    }

    /// Create an instance of [Simplifier].
    fn simplifier(&self) -> Simplifier {
        Simplifier::new(self.storages())
    }

    /// Create an instance of [Validator].
    fn validator(&self) -> Validator {
        Validator::new(self.storages())
    }

    /// Create an instance of [ScopeManager].
    fn scope_manager(&self) -> ScopeManager {
        ScopeManager::new(self.storages())
    }

    /// Create an instance of [PatMatcher].
    fn pat_matcher(&self) -> PatMatcher {
        PatMatcher::new(self.storages())
    }

    /// Create an instance of [ExhaustivenessChecker].
    fn exhaustiveness_checker(&self) -> ExhaustivenessChecker {
        ExhaustivenessChecker::new(self.storages())
    }

    /// Create an instance of [Discoverer].
    fn discoverer(&self) -> Discoverer {
        Discoverer::new(self.storages())
    }

    /// Create an instance of [CoreDefReader].
    fn core_defs(&self) -> CoreDefReader {
        CoreDefReader::new(self.storages())
    }
}

impl<T: AccessToStorage> AccessToOps for T {}
