use crate::keyword::Keyword;
use dashmap::DashMap;

use hash_utils::counter;
use lazy_static::lazy_static;
use strum::VariantNames;

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

#[derive(Debug)]
pub struct IdentifierMap {
    ident_data: DashMap<&'static str, Identifier>,
    path_ident_data: DashMap<&'static str, PathIdentifier>,
    path_ident_data_rev: DashMap<PathIdentifier, &'static str>,
    ident_data_rev: DashMap<Identifier, &'static str>,
}

lazy_static! {
    pub static ref IDENTIFIER_MAP: IdentifierMap = IdentifierMap::default();
}

// Ensure that keywords have exact identifier values...
// static_assertions::const_assert_eq!(*IDENTIFIER_MAP.ident_data.get("let").unwrap(), Identifier::from(Keyword::Let as u32));

pub struct PathIdentifierName(&'static str);

impl PathIdentifierName {
    pub fn full(&self) -> &str {
        self.0
    }

    pub fn components(&self) -> impl Iterator<Item = &str> {
        self.full().split("::")
    }
}

impl IdentifierMap {
    pub fn default() -> Self {
        let map = IdentifierMap {
            ident_data: DashMap::new(),
            path_ident_data: DashMap::new(),
            path_ident_data_rev: DashMap::new(),
            ident_data_rev: DashMap::new(),
        };

        // let wall = STATIC_CASTLE.wall();

        // Initialise the identifier map with all the keywords that are reserved in the language
        // so that it will be easier to perform comparisons on when a keyword is present, rather than
        // always looking them up. Thi smeans that the names of each keyword is guaranteed to have a
        // identifier value in the ranges of 0...15
        for keyword in Keyword::VARIANTS {
            // let value = BrickString::new(keyword, &wall);
            // map.create_ident(value);
            map.create_ident(Box::leak::<'static>((*keyword).to_owned().into_boxed_str()));
        }

        // assert_eq!(map.ident_name(Identifier::from(0)), "let".to_string());
        // assert_eq!(map.ident_name(Identifier::from(14)), "break".to_string());

        map
    }

    pub fn create_ident(&self, ident_str: &str) -> Identifier {
        if let Some(key) = self.ident_data.get(ident_str) {
            *key
        } else {
            let ident = Identifier::new();

            // let wall = STATIC_CASTLE.wall();
            // let ident_str_copy = BrickString::new(ident_str, &wall).as_str();
            let ident_str_copy = Box::leak::<'static>(ident_str.to_owned().into_boxed_str());

            self.ident_data.insert(ident_str_copy, ident);
            self.ident_data_rev.insert(ident, ident_str_copy);
            ident
        }
    }

    pub fn create_path_ident(&self, path_ident_str: &str) -> PathIdentifier {
        if let Some(key) = self.path_ident_data.get(path_ident_str) {
            *key
        } else {
            let path_ident = PathIdentifier::new();

            // let wall = STATIC_CASTLE.wall();
            // let path_ident_str_copy = BrickString::new(path_ident_str, &wall).as_str();
            let path_ident_str_copy = Box::leak(path_ident_str.to_owned().into_boxed_str());

            self.path_ident_data.insert(path_ident_str_copy, path_ident);
            self.path_ident_data_rev
                .insert(path_ident, path_ident_str_copy);
            path_ident
        }
    }

    pub fn ident_name(&self, ident: Identifier) -> &'static str {
        self.ident_data_rev.get(&ident).unwrap().value()
    }

    pub fn path_ident_name(&self, path_ident: PathIdentifier) -> PathIdentifierName {
        PathIdentifierName(self.path_ident_data_rev.get(&path_ident).unwrap().value())
    }
}
