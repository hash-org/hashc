use crate::types::TypeId;
use crate::{storage::GlobalStorage, writer::TypeWithStorage};
use hash_ast::ident::{Identifier, IDENTIFIER_MAP};
use hash_reporting::{
    errors::ErrorCode,
    reporting::{Report, ReportBuilder, ReportCodeBlock, ReportElement, ReportKind, ReportNote},
};
use hash_source::location::SourceLocation;

#[derive(Debug)]
pub enum Symbol {
    Compound {
        path: Vec<Identifier>,
        location: Option<SourceLocation>,
    },
    Single {
        symbol: Identifier,
        location: Option<SourceLocation>,
    },
}

impl Symbol {
    /// Function to get the identifier path/symbol from the entire [Symbol]
    pub fn get_ident(&self) -> Vec<Identifier> {
        match self {
            Symbol::Compound { path, .. } => path.to_vec(),
            Symbol::Single { symbol, .. } => vec![*symbol],
        }
    }

    pub fn location(&self) -> Option<SourceLocation> {
        match self {
            Symbol::Compound { location, .. } | Symbol::Single { location, .. } => *location,
        }
    }
}

// @@Todo: add ast node locations to these
#[derive(Debug)]
pub enum TypecheckError {
    TypeMismatch(TypeId, TypeId),
    UsingBreakOutsideLoop(SourceLocation),
    UsingContinueOutsideLoop(SourceLocation),
    UsingReturnOutsideFunction(SourceLocation),
    RequiresIrrefutablePattern(SourceLocation),
    UnresolvedSymbol(Symbol),
    TryingToNamespaceType(Symbol),
    TryingToNamespaceVariable(Symbol),
    SymbolIsNotAType(Symbol),
    SymbolIsNotAVariable(Symbol),
    SymbolIsNotATrait(Symbol),
    TypeIsNotStruct {
        ty: TypeId,
        location: SourceLocation,
        ty_def_location: Option<SourceLocation>,
    },
    UnresolvedStructField {
        field_name: Identifier,
        location: SourceLocation,
        ty_def_name: Identifier, // @@Maybe make this a symbol?
        ty_def_location: Option<SourceLocation>,
    },
    InvalidPropertyAccess {
        field_name: Identifier,
        location: SourceLocation,
        ty_def_name: Identifier,
        ty_def_location: Option<SourceLocation>,
    },
    ExpectingBooleanInCondition {
        found: TypeId,
        location: SourceLocation,
    },
    MissingStructField {
        field_name: Identifier,
        location: SourceLocation,
        ty_def_name: Identifier,
        ty_def_location: Option<SourceLocation>,
    },
    BoundRequiresStrictlyTypeVars(SourceLocation),
    ExpectingBindingForTraitImpl(SourceLocation),
    TraitDefinitionNotFound(Symbol),
    TypeAnnotationNotAllowedInTraitImpl(SourceLocation),
    TypeArgumentLengthMismatch {
        expected: usize,
        got: usize,
        location: Option<SourceLocation>,
    }, // @@TODO: length definition location
    NoMatchingTraitImplementations(Symbol),
    FunctionArgumentLengthMismatch {
        target: TypeId,
        source: TypeId,
        expected: usize,
        received: usize,
    },
}

pub type TypecheckResult<T> = Result<T, TypecheckError>;

impl TypecheckError {
    pub fn create_report(self, storage: &GlobalStorage<'_, '_>) -> Report {
        let mut builder = ReportBuilder::new();
        builder
            .with_kind(ReportKind::Error)
            .with_message("Failed to typecheck") // @@TODO: get general message for the appropriate error code
            .with_error_code(ErrorCode::Typecheck); // @@TODO: @@ErrorReporting: Get the correct typecheck code

        match self {
            TypecheckError::TypeMismatch(given, wanted) => {
                let given_ty = TypeWithStorage::new(given, storage);
                let given_ty_location = storage.types.get_location(given);
                let wanted_ty = TypeWithStorage::new(wanted, storage);
                let wanted_ty_location = storage.types.get_location(wanted);

                // @@TODO: Double notes on a CodeBlock instead of separate code blocks depending on proximity of spans
                if let Some(location) = wanted_ty_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        *location,
                        format!(
                            "This specificities that the expression should be of type `{}`",
                            wanted_ty
                        ),
                    )));
                }

                if let Some(location) = given_ty_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        *location,
                        format!("Found this to be of type `{}`", given_ty),
                    )));
                }

                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    format!(
                        "Types mismatch, got a `{}`, but wanted a `{}`.",
                        given_ty, wanted_ty
                    ),
                )));
            }
            TypecheckError::UsingBreakOutsideLoop(src) => {
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "here")))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        "You can't use a `break` clause outside of a loop.",
                    )));
            }
            TypecheckError::UsingContinueOutsideLoop(src) => {
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "here")))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        "You can't use a `continue` clause outside of a loop.",
                    )));
            }
            TypecheckError::UsingReturnOutsideFunction(src) => {
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "here")))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        "You can't use a `return` clause outside of a function body.",
                    )));
            }
            TypecheckError::RequiresIrrefutablePattern(src) => {
                builder
                .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "This pattern isn't refutable")))
                .add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    "Destructuring statements in `let` or `for` statements must use an irrefutable pattern.",
                )));
            }
            TypecheckError::UnresolvedSymbol(symbol) => {
                let ident_path = symbol.get_ident();
                let formatted_symbol = IDENTIFIER_MAP.get_path(ident_path.into_iter());

                if let Some(location) = symbol.location() {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "not found in this scope",
                    )));
                }

                // At-least we can print the symbol that wasn't found...
                builder.with_message(format!(
                    "Symbol `{}` is not defined in the current scope.",
                    formatted_symbol
                ));
            }
            TypecheckError::TryingToNamespaceType(symbol) => {
                let symbol_name = IDENTIFIER_MAP.get_path(symbol.get_ident().into_iter());

                if let Some(location) = symbol.location() {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!(
                            "This symbol `{}` is defined as a type in the current scope.",
                            symbol_name
                        ),
                    )));
                }

                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    "You cannot namespace a symbol that's a type.",
                )));
            }
            TypecheckError::TryingToNamespaceVariable(symbol) => {
                let symbol_name = IDENTIFIER_MAP.get_path(symbol.get_ident().into_iter());

                if let Some(location) = symbol.location() {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "This is a variable",
                    )));
                }

                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    format!("`{}` is a variable. You cannot namespace a variable defined in the current scope.", symbol_name),
                )));
            }
            TypecheckError::SymbolIsNotAType(symbol) => {
                let symbol_name = IDENTIFIER_MAP.get_path(symbol.get_ident().into_iter());

                if let Some(location) = symbol.location() {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "This expects a type.",
                    )));
                }

                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    format!("`{}` is not a type. You cannot use a trait or variable in the place of a type.", symbol_name),
                )));
            }
            TypecheckError::SymbolIsNotAVariable(symbol) => {
                let symbol_name = IDENTIFIER_MAP.get_path(symbol.get_ident().into_iter());

                if let Some(location) = symbol.location() {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "This expects a variable.",
                    )));
                }

                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    format!("`{}` is not a variable. You cannot use a type or trait in the place of a variable.", symbol_name),
                )));
            }
            TypecheckError::SymbolIsNotATrait(symbol) => {
                let symbol_name = IDENTIFIER_MAP.get_path(symbol.get_ident().into_iter());

                if let Some(location) = symbol.location() {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "This expects a trait.",
                    )));
                }

                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    format!("`{}` is not a trait. You cannot use a type or variable in the place of a trait.", symbol_name),
                )));
            }
            TypecheckError::TypeIsNotStruct {
                ty,
                location,
                ty_def_location,
            } => {
                let ty = TypeWithStorage::new(ty, storage);

                // Print where the original type is defined with an annotation.
                if let Some(ty_def_location) = ty_def_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        ty_def_location,
                        format!("The type `{}` is defined here.", ty),
                    )));
                }

                // Print where the literal being created...
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "Not a struct",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!("This type `{}` isn't a struct.", ty),
                    )));
            }
            TypecheckError::UnresolvedStructField {
                ty_def_location,
                ty_def_name,
                field_name,
                location,
            } => {
                let name = IDENTIFIER_MAP.get_ident(field_name);
                let ty_name = IDENTIFIER_MAP.get_ident(ty_def_name);

                // If we have the location of the definition, we can print it here
                if let Some(ty_def_location) = ty_def_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        ty_def_location,
                        format!("The struct `{}` is defined here.", ty_name),
                    )));
                }

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "Unknown field",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!(
                            "The field `{}` doesn't exist on struct `{}`.",
                            name, ty_name
                        ),
                    )));
            }
            TypecheckError::ExpectingBooleanInCondition { found, location } => {
                let found_ty = TypeWithStorage::new(found, storage);

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "Expression should be of `boolean` type",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!("In `if` statements, the condition must be explicitly of `boolean` type, however the expression was found to be of `{}` type.", found_ty),
                    )));
            }
            TypecheckError::MissingStructField {
                ty_def_location,
                ty_def_name,
                field_name,
                location: field_location,
            } => {
                let name = IDENTIFIER_MAP.get_ident(field_name);
                let ty_name = IDENTIFIER_MAP.get_ident(ty_def_name);

                // If we have the location of the definition, we can print it here
                if let Some(ty_def_location) = ty_def_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        ty_def_location,
                        format!("The struct `{}` is defined here.", ty_name),
                    )));
                }

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        field_location,
                        "Struct is missing field",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!("The struct `{}` is missing the field `{}`.", ty_name, name),
                    )));
            }
            TypecheckError::BoundRequiresStrictlyTypeVars(location) => {
                // @@TODO: Maybe report here what we found?
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location, "here",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        "This type bound should only contain type variables",
                    )));
            }
            TypecheckError::InvalidPropertyAccess {
                field_name,
                location,
                ty_def_name,
                ty_def_location,
            } => {
                let name = IDENTIFIER_MAP.get_ident(field_name);
                let ty_name = IDENTIFIER_MAP.get_ident(ty_def_name);

                // If we have the location of the definition, we can print it here
                if let Some(ty_def_location) = ty_def_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        ty_def_location,
                        format!("The struct `{}` is defined here.", ty_name),
                    )));
                }

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "unknown field",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!("The field `{}` doesn't exist on type `{}`.", name, ty_name),
                    )));
            }
            TypecheckError::ExpectingBindingForTraitImpl(loc) => {
                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    loc,
                    "Use a name binding here instead of a pattern.",
                )));

                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    "Only name bindings are allowed for let statements which are trait implementations.",
                )));
            }
            TypecheckError::TraitDefinitionNotFound(symbol) => {
                let ident_path = symbol.get_ident();
                let formatted_symbol = IDENTIFIER_MAP.get_path(ident_path.into_iter());

                if let Some(location) = symbol.location() {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "trait not found in this scope",
                    )));
                }

                // At-least we can print the symbol that wasn't found...
                builder.with_message(format!(
                    "Trait `{}` is not defined in the current scope.",
                    formatted_symbol
                ));
            }
            TypecheckError::TypeAnnotationNotAllowedInTraitImpl(loc) => {
                builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                    loc,
                    "Remove the type annotation here.",
                )));

                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    "Type annotations are not allowed for let statements which are trait implementations.",
                )));
            }
            TypecheckError::TypeArgumentLengthMismatch {
                expected,
                got,
                location,
            } => {
                if let Some(location) = location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        format!("Expected {} type arguments here.", expected),
                    )));
                }
                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    format!("Expected {} type arguments, but got {}.", expected, got),
                )));
                // @@Todo: it would be nice to have definition location here too.
            }
            TypecheckError::NoMatchingTraitImplementations(symbol) => {
                let trt_name = IDENTIFIER_MAP.get_path(symbol.get_ident().into_iter());

                if let Some(loc) = symbol.location() {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        loc,
                        format!("No matching implementations for '{}'.", trt_name),
                    )));
                }

                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    format!("There are no implementations of the trait '{}' that satisfy this invocation.", trt_name),
                )));
            }
            TypecheckError::FunctionArgumentLengthMismatch {
                // expected,
                source,
                target,
                expected,
                received,
            } => {
                let source_location = storage.types.get_location(source);
                let target_location = storage.types.get_location(target);

                builder.with_message(format!(
                    "Function argument mismatch, expected {} arguments, but got {}.",
                    expected, received
                ));

                if let Some(location) = source_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        *location,
                        "Function definition here".to_string(),
                    )));
                }

                if let Some(location) = target_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        *location,
                        "Arguments mismatch".to_string(),
                    )));
                }

                if expected > received {
                    let diff = expected - received;

                    builder.add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!("consider adding {} argument(s).", diff),
                    )));
                } else {
                    let diff = received - expected;

                    if diff == 1 {
                        // @@Reporting: suggestions!
                        builder.add_element(ReportElement::Note(ReportNote::new(
                            "note",
                            "consider removing the last argument.".to_string(),
                        )));
                    } else {
                        builder.add_element(ReportElement::Note(ReportNote::new(
                            "note",
                            format!("consider removing the last {} arguments.", diff),
                        )));
                    }
                }
            }
        }

        builder.build().unwrap()
    }
}
