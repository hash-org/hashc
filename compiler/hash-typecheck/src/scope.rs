//! All rights reserved 2022 (c) The Hash Language authors
use crate::error::{Symbol, TypecheckError, TypecheckResult};
use crate::storage::GlobalStorage;
use crate::traits::TraitId;
use crate::types::{PrimType, TypeDefId, TypeId, TypeStorage, TypeValue};
use hash_ast::{
    ast::AccessName,
    ident::{Identifier, IDENTIFIER_MAP},
};
use hash_source::{location::SourceLocation, SourceId};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolType {
    Variable(TypeId),
    EnumVariant(TypeDefId),
    Type(TypeId),
    TypeDef(TypeDefId),
    Trait(TraitId),
}

#[derive(Debug, Default, Clone)]
pub struct Scope {
    symbols: HashMap<Identifier, SymbolType>,
}

impl Scope {
    pub fn root(global_storage: &mut GlobalStorage) -> Self {
        let mut scope = Self::new();

        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("usize"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::USize), None),
            ),
        );

        // Create the boolean type
        let bool_ty_id = global_storage
            .types
            .create(TypeValue::Prim(PrimType::Bool), None);

        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("bool"),
            SymbolType::Type(bool_ty_id),
        );

        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("false"),
            SymbolType::Variable(bool_ty_id),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("true"),
            SymbolType::Variable(bool_ty_id),
        );

        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("u8"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::U8), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("u16"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::U16), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("u32"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::U32), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("u64"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::U64), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("isize"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::ISize), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("i8"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::I8), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("i16"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::I16), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("i32"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::I32), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("i64"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::I64), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("f32"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::F32), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("f64"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::F64), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("char"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::Char), None),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("void"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::Void), None),
            ),
        );

        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("str"),
            SymbolType::TypeDef(global_storage.core_type_defs.str),
        );

        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("List"),
            SymbolType::TypeDef(global_storage.core_type_defs.list),
        );

        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("Map"),
            SymbolType::TypeDef(global_storage.core_type_defs.map),
        );

        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("Set"),
            SymbolType::TypeDef(global_storage.core_type_defs.set),
        );

        scope
    }

    pub fn new() -> Self {
        Self::default()
    }

    pub fn resolve_symbol(&self, symbol: Identifier) -> Option<SymbolType> {
        self.symbols.get(&symbol).copied()
    }

    pub fn add_symbol(&mut self, symbol: Identifier, symbol_type: SymbolType) {
        // @@TODO: naming clashes
        self.symbols.insert(symbol, symbol_type);
    }
}

#[derive(Debug, Clone)]
pub struct ScopeStack {
    scopes: Vec<Scope>,
}

impl ScopeStack {
    pub fn empty() -> Self {
        Self {
            scopes: vec![Scope::new()],
        }
    }
    pub fn new(global_storage: &mut GlobalStorage) -> Self {
        let root_scope = Scope::root(global_storage);
        Self {
            scopes: vec![root_scope, Scope::new()],
        }
    }
    pub fn with_scopes(
        global_storage: &mut GlobalStorage,
        scopes: impl Iterator<Item = Scope>,
    ) -> Self {
        let mut stack = Self::new(global_storage);
        stack.scopes.extend(scopes);
        stack
    }

    pub fn resolve_symbol(&self, symbol: Identifier) -> Option<SymbolType> {
        for scope in self.iter_up() {
            if let Some(symbol_type) = scope.resolve_symbol(symbol) {
                return Some(symbol_type);
            }
        }

        None
    }

    pub fn append(&mut self, other: ScopeStack) {
        self.scopes.extend(other.scopes);
    }

    pub fn add_symbol(&mut self, symbol: Identifier, symbol_type: SymbolType) {
        self.current_scope_mut().add_symbol(symbol, symbol_type);
    }

    pub fn current_scope(&self) -> &Scope {
        self.scopes.last().unwrap()
    }

    pub fn extract_current_scope(&mut self) -> Scope {
        self.scopes.pop().unwrap()
    }

    pub fn current_scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    pub fn enter_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    pub fn iter_up(&self) -> impl Iterator<Item = &Scope> {
        self.scopes.iter().rev()
    }

    pub fn iter_up_mut(&mut self) -> impl Iterator<Item = &mut Scope> {
        self.scopes.iter_mut().rev()
    }

    pub fn pop_scope(&mut self) -> Scope {
        match self.scopes.pop() {
            Some(scope) => scope,
            None => panic!("Cannot pop root scope"),
        }
    }
}

pub fn resolve_compound_symbol(
    scopes: &ScopeStack,
    types: &TypeStorage,
    symbols: &AccessName<'_>,
    source_id: SourceId,
) -> TypecheckResult<(Identifier, SymbolType)> {
    let mut last_scope = scopes;
    let symbol_path = symbols.path_with_locations();
    let mut symbols_iter = symbol_path.iter().enumerate().peekable();

    loop {
        match symbols_iter.next() {
            Some((i, &(symbol, symbol_location))) => {
                let location = SourceLocation {
                    location: symbol_location,
                    source_id,
                };

                match last_scope.resolve_symbol(symbol) {
                    Some(symbol_ty @ SymbolType::Variable(type_id)) => match types.get(type_id) {
                        TypeValue::Namespace(namespace_ty) if symbols_iter.peek().is_some() => {
                            last_scope = &namespace_ty.members;
                            continue;
                        }
                        TypeValue::Namespace(_) => {
                            return Ok((symbol, symbol_ty));
                        }
                        _ if symbols_iter.peek().is_some() => {
                            return Err(TypecheckError::TryingToNamespaceVariable(
                                Symbol::Compound {
                                    path: symbols.path()[..=i].to_owned(),
                                    location: Some(location),
                                },
                            ));
                        }
                        _ => {
                            return Ok((symbol, symbol_ty));
                        }
                    },
                    Some(_) if symbols_iter.peek().is_some() => {
                        return Err(TypecheckError::TryingToNamespaceType(Symbol::Compound {
                            path: symbols.path()[..=i].to_owned(),
                            location: Some(location),
                        }));
                    }
                    Some(symbol_ty) => {
                        return Ok((symbol, symbol_ty));
                    }
                    None => {
                        return Err(TypecheckError::UnresolvedSymbol(Symbol::Compound {
                            path: symbols.path()[..=i].to_owned(),
                            location: Some(location),
                        }))
                    }
                }
            }
            None => unreachable!(),
        }
    }
}
