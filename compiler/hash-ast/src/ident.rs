use std::collections::HashMap;
use hash_utils::counter;
use crate::ast::AstString;

counter! {
    name: Identifier,
    counter_name: IDENTIFIER_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug, Default)]
pub struct IdentifierMap {
    data: HashMap<Identifier, AstString>,
}

impl IdentifierMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn create(&mut self, ident_str: AstString) -> Identifier {
        let ident = Identifier::new();
        self.data.insert(ident, ident_str);
        ident
    }

    pub fn get_name(&self, ident: Identifier) -> &str {
        self.data.get(&ident).unwrap()
    }
}

counter! {
    name: PathIdentifier,
    counter_name: PATH_IDENTIFIER_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug, Default)]
pub struct PathIdentifierMap {
    data: HashMap<PathIdentifier, AstString>,
}

impl PathIdentifierMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn create(&mut self, path_ident_str: AstString) -> PathIdentifier {
        let ident = PathIdentifier::new();
        self.data.insert(ident, path_ident_str);
        ident
    }

    pub fn components(&self, path_ident: PathIdentifier) -> impl Iterator<Item=&str> {
        self.data.get(&path_ident).unwrap().split("::")
    }
}


