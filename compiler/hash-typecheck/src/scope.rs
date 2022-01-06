use crate::error::{TypecheckError, TypecheckResult};
use crate::storage::GlobalStorage;
use crate::types::{PrimType, TypeDefId, TypeId, TypeValue, Types};
use hash_ast::ident::{Identifier, IDENTIFIER_MAP};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolType {
    Variable(TypeId),
    Type(TypeId),
    TypeDef(TypeDefId),
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
                    .create(TypeValue::Prim(PrimType::USize)),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("bool"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::Bool))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("u8"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::U8))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("u16"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::U16))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("u32"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::U32))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("u64"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::U64))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("isize"),
            SymbolType::Type(
                global_storage
                    .types
                    .create(TypeValue::Prim(PrimType::ISize)),
            ),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("i8"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::I8))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("i16"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::I16))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("i32"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::I32))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("i64"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::I64))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("f32"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::F32))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("f64"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::F64))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("char"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::Char))),
        );
        scope.add_symbol(
            IDENTIFIER_MAP.create_ident("void"),
            SymbolType::Type(global_storage.types.create(TypeValue::Prim(PrimType::Void))),
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
        self.symbols.get(&symbol).map(|&s| s)
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
    types: &Types,
    symbols: &[Identifier],
) -> TypecheckResult<SymbolType> {
    let mut last_scope = scopes;
    let mut symbols_iter = symbols.iter().enumerate().peekable();

    loop {
        match symbols_iter.next() {
            Some((i, &symbol)) => match last_scope.resolve_symbol(symbol) {
                Some(symbol_ty @ SymbolType::Variable(type_id)) => match types.get(type_id) {
                    TypeValue::Namespace(namespace_ty) if symbols_iter.peek().is_some() => {
                        last_scope = &namespace_ty.members;
                        continue;
                    }
                    TypeValue::Namespace(_) => {
                        return Ok(symbol_ty);
                    }
                    _ if symbols_iter.peek().is_some() => {
                        return Err(TypecheckError::TryingToNamespaceVariable(
                            symbols[..=i].to_owned(),
                        ));
                    }
                    _ => {
                        return Ok(symbol_ty);
                    }
                },
                Some(_) if symbols_iter.peek().is_some() => {
                    return Err(TypecheckError::TryingToNamespaceType(
                        symbols[..=i].to_owned(),
                    ));
                }
                Some(symbol_ty) => {
                    return Ok(symbol_ty);
                }
                None => return Err(TypecheckError::UnresolvedSymbol(symbols[..=i].to_owned())),
            },
            None => unreachable!(),
        }
    }
}
