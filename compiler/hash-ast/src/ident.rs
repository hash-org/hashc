use crate::ast::AstString;
use dashmap::DashMap;
use hash_utils::counter;
use lazy_static::lazy_static;
use std::sync::atomic::{AtomicBool, Ordering};

counter! {
    name: Identifier,
    counter_name: IDENTIFIER_COUNTER,
    visibility: pub,
    method_visibility:,
}

counter! {
    name: PathIdentifier,
    counter_name: PATH_IDENTIFIER_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug, Default)]
pub struct IdentifierMap {
    ident_data: DashMap<AstString, Identifier>,
    path_ident_data: DashMap<AstString, PathIdentifier>,
    path_ident_data_rev: DashMap<PathIdentifier, AstString>,
    ident_data_rev: DashMap<Identifier, AstString>,
    revs_computed: AtomicBool,
}

lazy_static! {
    pub static ref IDENTIFIER_MAP: IdentifierMap = IdentifierMap::default();
}

pub struct PathIdentifierName(String);

impl PathIdentifierName {
    pub fn full(&self) -> &str {
        self.0.as_ref()
    }

    pub fn components(&self) -> impl Iterator<Item = &str> {
        self.full().split("::")
    }
}

impl IdentifierMap {
    pub fn create_ident(&self, ident_str: AstString) -> Identifier {
        if let Some(key) = self.ident_data.get(&ident_str) {
            *key
        } else {
            let ident = Identifier::new();
            self.ident_data.insert(ident_str, ident);
            ident
        }
    }

    pub fn create_path_ident(&self, path_ident_str: AstString) -> PathIdentifier {
        if let Some(key) = self.path_ident_data.get(&path_ident_str) {
            *key
        } else {
            let path_ident = PathIdentifier::new();
            self.path_ident_data.insert(path_ident_str, path_ident);
            path_ident
        }
    }

    pub fn compute_reverses(&self) {
        for entry in self.ident_data.iter() {
            self.ident_data_rev
                .insert(entry.value().to_owned(), entry.key().to_owned());
        }

        for entry in self.path_ident_data.iter() {
            self.path_ident_data_rev
                .insert(entry.value().to_owned(), entry.key().to_owned());
        }
    }

    fn ensure_reverses_computed(&self) {
        if !self.revs_computed.load(Ordering::SeqCst) {
            panic!("Tried to access reverses but they have not been computed")
        }
    }

    pub fn ident_name(&self, ident: Identifier) -> String {
        self.ensure_reverses_computed();
        self.ident_data_rev.get(&ident).unwrap().value().to_string()
    }

    pub fn path_ident_name(&self, path_ident: PathIdentifier) -> PathIdentifierName {
        self.ensure_reverses_computed();
        PathIdentifierName(
            self.path_ident_data_rev
                .get(&path_ident)
                .unwrap()
                .value()
                .to_string(),
        )
    }
}
