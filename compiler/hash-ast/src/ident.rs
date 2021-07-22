use crate::ast::AstString;
use dashmap::DashMap;
use hash_utils::counter;
use lazy_static::lazy_static;

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
}

lazy_static! {
    // @@Improvement: Initialise the identifier map with all the keywords that are reserved in the language
    //                so that it will be easier to perform comparisons on when a keyword is present, rather than
    //                always looking them up...
    pub static ref IDENTIFIER_MAP: IdentifierMap = IdentifierMap::default();
}

pub struct PathIdentifierName(AstString);

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
            let ident_str_cpy = ident_str.clone();
            self.ident_data.insert(ident_str, ident);
            self.ident_data_rev.insert(ident, ident_str_cpy);
            ident
        }
    }

    pub fn create_path_ident(&self, path_ident_str: AstString) -> PathIdentifier {
        if let Some(key) = self.path_ident_data.get(&path_ident_str) {
            *key
        } else {
            let path_ident = PathIdentifier::new();
            let path_ident_str_cpy = path_ident_str.clone();
            self.path_ident_data.insert(path_ident_str, path_ident);
            self.path_ident_data_rev
                .insert(path_ident, path_ident_str_cpy);
            path_ident
        }
    }

    pub fn ident_name(&self, ident: Identifier) -> String {
        self.ident_data_rev.get(&ident).unwrap().value().to_string()
    }

    pub fn path_ident_name(&self, path_ident: PathIdentifier) -> PathIdentifierName {
        PathIdentifierName(
            self.path_ident_data_rev
                .get(&path_ident)
                .unwrap()
                .value()
                .clone(),
        )
    }
}
