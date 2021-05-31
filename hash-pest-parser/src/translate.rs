//! Hash compiler module for converting from tokens to an AST tree
//!
//! All rights reserved 2021 (c) The Hash Language authors

use crate::{
    grammar::{HashPair, Rule},
    precedence::climb,
    utils::convert_rule_into_fn_call,
};
use hash_ast::{
    ast::*,
    error::{ParseError, ParseResult},
    location::Location,
    parse::{IntoAstNode, ModuleResolver},
};
use num::BigInt;
use std::vec;

/// Utility for creating a boolean in enum representation
fn make_boolean(variant: bool, ab: &AstBuilder) -> AstNode<AccessName> {
    let name_ref = String::from(match variant {
        false => "false",
        true => "true",
    });

    ab.node(AccessName {
        names: vec![ab.node(Name { string: name_ref })],
    })
}

/// Utility finction for creating a variable from a given name.
fn make_variable(name: AstNode<AccessName>, ab: &AstBuilder) -> AstNode<Expression> {
    ab.node(Expression::Variable(VariableExpr {
        name,
        type_args: vec![],
    }))
}

/// Utility function to make an `$internal` identifier reference, this is used when
/// transforming assignment with update operators like `+=`
fn make_internal_node(ab: &AstBuilder) -> AstNode<Expression> {
    ab.node(Expression::Variable(VariableExpr {
        name: ab.node(AccessName {
            names: vec![ab.node(Name {
                string: String::from("$internal"),
            })],
        }),
        type_args: vec![],
    }))
}

/// A wrapper around AstNode to build [AstNode]s with the same information as the builder
/// holds. Creating new [AstNode]s with the the builder will copy over the [ModuleIndex]
/// and the [Location] of the node. An [AstBuilder] can be created from an existing node,
/// or a [pest::iterators::Pair].
pub struct AstBuilder {
    pos: Location,
}

impl AstBuilder {
    pub fn from_pair(pair: &pest::iterators::Pair<'_, Rule>) -> AstBuilder {
        let span = pair.as_span();
        let pos = Location::Span(span.start(), span.end());
        AstBuilder { pos }
    }

    /// Create an [AstBuilder] from an [AstNode]
    pub fn from_node<T>(node: &AstNode<T>) -> AstBuilder {
        AstBuilder { pos: node.pos }
    }

    /// Create a new [AstNode] from the information provided by the [AstBuilder]
    pub fn node<T>(&self, inner: T) -> AstNode<T> {
        AstNode {
            body: Box::new(inner),
            pos: self.pos,
        }
    }

    pub fn error(&self, message: String) -> ParseError {
        ParseError::AstGeneration {
            location: self.pos,
            message,
        }
    }
}

macro_rules! pair_to_ast {
    ($pair:expr, $resolver:expr) => {
        HashPair::from_inner($pair).into_ast($resolver)
    };
}

macro_rules! pairs_to_asts {
    ($pairs:expr, $resolver:expr) => {
        $pairs
            .map(|p| HashPair::from_inner(p).into_ast($resolver))
            .collect::<Result<Vec<_>, _>>()
    };
}

impl IntoAstNode<Name> for HashPair<'_> {
    fn into_ast(self, _: &mut impl ModuleResolver) -> ParseResult<AstNode<Name>> {
        match self.inner().as_rule() {
            Rule::ident => Ok(AstBuilder::from_pair(&self.inner()).node(Name {
                string: self.inner().as_str().to_owned(),
            })),
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<StructDefEntry> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<StructDefEntry>> {
        match self.inner().as_rule() {
            Rule::struct_def_field => {
                let ab = AstBuilder::from_pair(&self.inner());
                let mut components = self.into_inner().into_inner();

                let name = pair_to_ast!(components.next().unwrap(), resolver)?;
                let next_node = components.next();

                let (ty, def) = match next_node {
                    Some(pair) => match pair.as_rule() {
                        Rule::any_type => (
                            Some(pair_to_ast!(pair, resolver)?),
                            components
                                .next()
                                .map(|p| pair_to_ast!(p, resolver))
                                .transpose()?,
                        ),
                        Rule::expr => (None, Some(pair_to_ast!(pair, resolver)?)),
                        k => panic!("unexpected rule within literal_pattern: {:?}", k),
                    },
                    None => (None, None),
                };

                Ok(ab.node(StructDefEntry {
                    name,
                    ty,
                    default: def,
                }))
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<StructLiteralEntry> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<StructLiteralEntry>> {
        match self.inner().as_rule() {
            Rule::struct_literal_field => {
                let ab = AstBuilder::from_pair(&self.inner());
                let mut components = self.into_inner().into_inner();

                let name = pair_to_ast!(components.next().unwrap(), resolver)?;
                let value = pair_to_ast!(components.next().unwrap(), resolver)?;

                Ok(ab.node(StructLiteralEntry { name, value }))
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<EnumDefEntry> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<EnumDefEntry>> {
        match self.inner().as_rule() {
            Rule::enum_field => {
                let ab = AstBuilder::from_pair(&self.inner());
                let mut components = self.into_inner().into_inner();

                let name = pair_to_ast!(components.next().unwrap(), resolver)?;
                let args = pairs_to_asts!(components, resolver)?;

                Ok(ab.node(EnumDefEntry { name, args }))
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<Bound> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<Bound>> {
        match self.inner().as_rule() {
            Rule::bound => {
                let ab = AstBuilder::from_pair(&self.inner());
                let mut components = self.into_inner().into_inner();

                // firsly convertkk the type args by just iterating the inner component
                // of the type_args rule...
                let type_args: Vec<AstNode<Type>> =
                    pairs_to_asts!(components.next().unwrap().into_inner(), resolver)?;

                // check if there are any trait_bounds attached with this bound
                let trait_bounds = match components.next() {
                    Some(pair) => pairs_to_asts!(pair.into_inner(), resolver)?,
                    None => vec![],
                };

                Ok(ab.node(Bound {
                    type_args,
                    trait_bounds,
                }))
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<TraitBound> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<TraitBound>> {
        match self.inner().as_rule() {
            Rule::trait_bound => {
                let ab = AstBuilder::from_pair(self.inner());
                let mut components = self.into_inner().into_inner();

                // convert the access_name rule into a AstNode, each trait bound is guaranteed
                // to have an access name, so it's safe to unwrap here...
                let name = pair_to_ast!(components.next().unwrap(), resolver)?;

                // convert any type args the trait bound contains
                let type_args = match components.next() {
                    Some(pair) => pairs_to_asts!(pair.into_inner(), resolver)?,
                    None => vec![],
                };

                Ok(ab.node(TraitBound { name, type_args }))
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<AccessName> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<AccessName>> {
        match self.inner().as_rule() {
            Rule::access_name => Ok(AstBuilder::from_pair(&self.inner()).node(AccessName {
                names: pairs_to_asts!(self.into_inner().into_inner(), resolver)?,
            })),
            _ => unreachable!(),
        }
    }
}

const FUNCTION_TYPE_NAME: &str = "Function";
const TUPLE_TYPE_NAME: &str = "Tuple";
const LIST_TYPE_NAME: &str = "List";
const SET_TYPE_NAME: &str = "Set";
const MAP_TYPE_NAME: &str = "Map";

fn single_access_name(ab: &AstBuilder, name: &str) -> AstNode<AccessName> {
    ab.node(AccessName {
        names: vec![ab.node(Name {
            string: name.to_owned(),
        })],
    })
}

impl IntoAstNode<Type> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<Type>> {
        match self.inner().as_rule() {
            Rule::any_type => {
                let ab = AstBuilder::from_pair(&self.inner());
                let in_type = self.into_inner().into_inner().next().unwrap();
                match in_type.as_rule() {
                    Rule::infer_type => Ok(ab.node(Type::Infer)),
                    Rule::named_type => {
                        let mut in_named = in_type.into_inner();

                        let name = pair_to_ast!(in_named.next().unwrap(), resolver)?;
                        let type_args = in_named
                            .next()
                            .map(|n| pairs_to_asts!(n.into_inner(), resolver))
                            .unwrap_or(Ok(vec![]))?;

                        Ok(ab.node(Type::Named(NamedType { name, type_args })))
                    }
                    Rule::fn_type => {
                        let mut in_func = in_type.into_inner();

                        let mut args = pairs_to_asts!(in_func
                            .next()
                            .unwrap()
                            .into_inner(), resolver)?;
                        let ret = pair_to_ast!(in_func.next().unwrap(), resolver)?;
                        args.push(ret);

                        Ok(ab.node(Type::Named(NamedType {
                            name: single_access_name(&ab, FUNCTION_TYPE_NAME),
                            type_args: args,
                        })))
                    }
                    Rule::tuple_type => {
                        let inner = pairs_to_asts!(in_type.into_inner(), resolver)?;
                        Ok(ab.node(Type::Named(NamedType {
                            name: single_access_name(&ab, TUPLE_TYPE_NAME),
                            type_args: inner,
                        })))
                    }
                    Rule::list_type => {
                        let inner = pairs_to_asts!(in_type.into_inner(), resolver)?;

                        // list type should only have one type
                        debug_assert_eq!(inner.len(), 1);

                        Ok(ab.node(Type::Named(NamedType {
                            name: single_access_name(&ab, LIST_TYPE_NAME),
                            type_args: inner,
                        })))
                    }
                    Rule::set_type => {
                        let inner = pairs_to_asts!(in_type.into_inner(), resolver)?;

                        // set type should only have one type
                        debug_assert_eq!(inner.len(), 1);

                        Ok(ab.node(Type::Named(NamedType {
                            name: single_access_name(&ab, SET_TYPE_NAME),
                            type_args: inner,
                        })))
                    }
                    Rule::map_type => {
                        let inner: Vec<AstNode<Type>> =
                            pairs_to_asts!(in_type.into_inner(), resolver)?;

                        // map type should only have a type for a key and a value
                        debug_assert_eq!(inner.len(), 2);

                        Ok(ab.node(Type::Named(NamedType {
                            name: single_access_name(&ab, MAP_TYPE_NAME),
                            type_args: inner,
                        })))
                    }
                    Rule::existential_type => Ok(ab.node(Type::Existential)),
                    _ => unreachable!(),
                }
            }
            k => panic!("unexpected rule within type: {:?} at {:?}", k, self.inner()),
        }
    }
}

impl IntoAstNode<Literal> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<Literal>> {
        let ab = AstBuilder::from_pair(&self.inner());

        match self.inner().as_rule() {
            // If the literal is wrapped in a literal_expr, we unwrap it and then just convert
            // the internal contents of it using the same implementation...
            Rule::literal_expr => pair_to_ast!(self.into_inner().into_inner().next().unwrap(), resolver),
            Rule::integer_literal => {
                let inner = self.into_inner().into_inner().next().unwrap();
                // this could be binary, hex, octal or decimal...
                match inner.as_rule() {
                    Rule::decimal_literal => {
                        // check if there is a float exp component since we allow this, although if the specified exponent is
                        // float, we'll cast the result to decimal...
                        let mut components = inner.into_inner();
                        let num = components.next().unwrap();

                        let val = BigInt::parse_bytes(num.as_str().as_bytes(), 10).unwrap();

                        Ok(ab.node(Literal::Int(val)))
                    }
                    Rule::hex_literal => {
                        let item = inner.into_inner().next().unwrap();
                        let val = BigInt::parse_bytes(item.as_str().as_bytes(), 16).unwrap();
                        Ok(ab.node(Literal::Int(val)))
                    }
                    Rule::octal_literal => {
                        let item = inner.into_inner().next().unwrap();
                        let val = BigInt::parse_bytes(item.as_str().as_bytes(), 8).unwrap();
                        Ok(ab.node(Literal::Int(val)))
                    }
                    Rule::bin_literal => {
                        let item = inner.into_inner().next().unwrap();
                        let val = BigInt::parse_bytes(item.as_str().as_bytes(), 2).unwrap();
                        Ok(ab.node(Literal::Int(val)))
                    }
                    _ => unreachable!(),
                }
            }
            Rule::float_literal => {
                let mut components = self.into_inner().into_inner();

                // float_literal is made of three parts, the integer part, fractical part
                // and an optional exponent part...
                let float = components.next().unwrap();

                let mut value: f64 = float
                    .as_str()
                    .parse()
                    .map_err(|_| ab.error("Invalid float literal.".to_owned()))?;

                // apply exponent if any
                value = match components.next() {
                    Some(pair) => {
                        // since it might also have a -/+ sign, we need join it with the exponent int literal...
                        // @@Speed: is this a good way of joining strings...?
                        let str_val = pair.into_inner().map(|p| p.as_str()).collect::<String>();

                        let exponent: i32 = str_val
                            .parse()
                            .unwrap_or_else(|_| panic!("Invalid float exp: {}", str_val)); // @@Incomplete: change this to report an ast error!

                        value.powi(exponent)
                    }
                    None => value,
                };

                Ok(ab.node(Literal::Float(value)))
            }
            Rule::char_literal => {
                // we need to get the second character in the literal because the first one will be the character quote, since pest includes them in the span
                let c: char = self.inner().as_str().chars().nth(1).unwrap();
                Ok(ab.node(Literal::Char(c)))
            }
            Rule::string_literal => {
                let s = String::from(self.into_inner().into_inner().next().unwrap().as_str());
                Ok(ab.node(Literal::Str(s)))
            }
            Rule::list_literal => {
                // since list literals are just a bunch of expressions, we just call
                // into_ast(resolver) on each member and collect at the end
                let elements = pairs_to_asts!(self.into_inner().into_inner(), resolver)?;

                Ok(ab.node(Literal::List(ListLiteral { elements })))
            }
            Rule::set_literal => {
                // since set literals are just a bunch of expressions, we just call
                // into_ast(resolver) on each member and collect at the end
                let elements = pairs_to_asts!(self.into_inner().into_inner(), resolver)?;

                Ok(ab.node(Literal::Set(SetLiteral { elements })))
            }
            Rule::tuple_literal => {
                // since tuple literals are just a bunch of expressions, we just call
                // into_ast(resolver) on each member and collect at the end
                let elements = pairs_to_asts!(self.into_inner().into_inner(), resolver)?;

                Ok(ab.node(Literal::Tuple(TupleLiteral { elements })))
            }
            Rule::map_literal => {
                // A map is made of a vector of 'map_entries' rules, which are just two
                // expressions.
                let elements = self
                    .into_inner()
                    .into_inner()
                    .map(|p| {
                        let mut items = p.into_inner().map(|p| pair_to_ast!(p, resolver));
                        Ok((items.next().unwrap()?, items.next().unwrap()?))
                    })
                    .collect::<Result<_, ParseError>>()?;

                Ok(ab.node(Literal::Map(MapLiteral { elements })))
            }
            Rule::fn_literal => {
                // we're looking for a number of function arguments, an optional return and
                // a function body which is just an expression.
                let mut components = self.into_inner().into_inner();

                // firstly, take care of the function parameters...
                let args = components
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|param| {
                        let mut param_components = param.into_inner();

                        // get the name of identifier
                        let name = pair_to_ast!(param_components.next().unwrap(), resolver)?;

                        // if no type is specified for the param, we just set it to none
                        let ty = param_components
                            .next()
                            .map(|t| pair_to_ast!(t, resolver))
                            .transpose()?;

                        Ok(ab.node(FunctionDefArg { name, ty }))
                    })
                    .collect::<Result<_, ParseError>>()?;

                // now check here if the next rule is either a type or a expression,
                // if it is a type, we expect that there are two more rules to follow
                // since function literals cannot be without a fn_body
                let fn_type_or_body = components.next().unwrap();

                let (return_ty, fn_body) = match fn_type_or_body.as_rule() {
                    Rule::any_type => {
                        let body = components.next().unwrap();
                        (
                            Some(pair_to_ast!(fn_type_or_body, resolver)?),
                            pair_to_ast!(body, resolver)?,
                        )
                    }
                    Rule::fn_body => (None, pair_to_ast!(fn_type_or_body, resolver)?),
                    k => panic!("unexpected rule within fn_literal: {:?}", k),
                };
                Ok(ab.node(Literal::Function(FunctionDef {
                    args,
                    return_ty,
                    fn_body,
                })))
            }
            Rule::struct_literal => {
                let mut components = self.into_inner().into_inner();

                // first sort out the name of the struct
                let name = pair_to_ast!(components.next().unwrap(), resolver)?;

                // now check if the next rule is either type_args or struct_fields...
                let type_args_or_fields = components.next().unwrap();

                let (type_args, entries) = match type_args_or_fields.as_rule() {
                    Rule::type_args => {
                        // convert the type args into ast nodes...
                        let type_args = pairs_to_asts!(type_args_or_fields.into_inner(), resolver)?;

                        // convert the struct fields into ast nodes...
                        let fields =
                            pairs_to_asts!(components.next().unwrap().into_inner(), resolver)?;

                        (type_args, fields)
                    }
                    Rule::struct_literal_fields => (
                        vec![],
                        pairs_to_asts!(type_args_or_fields.into_inner(), resolver)?,
                    ),
                    k => panic!("unexpected rule within struct_literal: {:?}", k),
                };

                Ok(ab.node(Literal::Struct(StructLiteral {
                    name,
                    type_args,
                    entries,
                })))
            }
            k => panic!(
                "unexpected rule within literal: {:?} at {:?}",
                k,
                self.inner()
            ),
        }
    }
}

impl IntoAstNode<LiteralPattern> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<LiteralPattern>> {
        match self.inner().as_rule() {
            Rule::literal_pattern => {
                let pat = self.into_inner().into_inner().next().unwrap();

                // we prematurely convert the first node into a Literal, and then
                // pattern match on the literal, converting into a Literal pattern
                let node: AstNode<Literal> = pair_to_ast!(pat, resolver)?;
                let builder = AstBuilder::from_node(&node);

                // essentially cast the literal into a literal_pattern
                Ok(match *node.body {
                    Literal::Str(s) => builder.node(LiteralPattern::Str(s)),
                    Literal::Char(s) => builder.node(LiteralPattern::Char(s)),
                    Literal::Float(s) => builder.node(LiteralPattern::Float(s)),
                    Literal::Int(s) => builder.node(LiteralPattern::Int(s)),
                    k => panic!(
                        "literal_pattern should be string, float, char or int, got : {:?}",
                        k
                    ),
                })
            }
            k => panic!("unexpected rule within literal_pattern: {:?}", k),
        }
    }
}

impl IntoAstNode<Pattern> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<Pattern>> {
        let ab = AstBuilder::from_pair(&self.inner());

        match self.inner().as_rule() {
            Rule::pattern => pair_to_ast!(self.into_inner().into_inner().next().unwrap(), resolver),
            Rule::single_pattern => {
                let pat = self.into_inner().into_inner().next().unwrap();

                match pat.as_rule() {
                    Rule::enum_pattern => {
                        let mut components = pat.into_inner();

                        let name = pair_to_ast!(components.next().unwrap(), resolver)?;
                        let args =
                            pairs_to_asts!(components.next().unwrap().into_inner(), resolver)?;

                        Ok(ab.node(Pattern::Enum(EnumPattern { name, args })))
                    }
                    Rule::struct_pattern => {
                        let mut components = pat.into_inner();

                        let name = pair_to_ast!(components.next().unwrap(), resolver)?;

                        // If there is no binding part of the destructuring pattern, as in if
                        // no pattern on the right-handside, we use the name of the field as a
                        // binding pattern here...
                        let entries = components
                            .next()
                            .unwrap()
                            .into_inner()
                            .map(|p| {
                                let mut field = p.into_inner();

                                let name: AstNode<Name> =
                                    pair_to_ast!(field.next().unwrap(), resolver)?;

                                let pattern = match field.next() {
                                    Some(pat) => pair_to_ast!(pat, resolver)?,
                                    None => AstBuilder::from_node(&name)
                                        .node(Pattern::Binding(name.clone())),
                                };

                                Ok(AstBuilder::from_node(&name)
                                    .node(DestructuringPattern { name, pattern }))
                            })
                            .collect::<Result<_, ParseError>>()?;

                        Ok(ab.node(Pattern::Struct(StructPattern { name, entries })))
                    }
                    Rule::namespace_pattern => {
                        let patterns = pat
                            .into_inner()
                            .map(|p| {
                                let mut field = p.into_inner();

                                let name: AstNode<Name> =
                                    pair_to_ast!(field.next().unwrap(), resolver)?;

                                let pattern = match field.next() {
                                    Some(pat) => pair_to_ast!(pat, resolver)?,
                                    None => AstBuilder::from_node(&name)
                                        .node(Pattern::Binding(name.clone())),
                                };

                                Ok(AstBuilder::from_node(&name)
                                    .node(DestructuringPattern { name, pattern }))
                            })
                            .collect::<Result<_, ParseError>>()?;

                        Ok(ab.node(Pattern::Namespace(NamespacePattern { patterns })))
                    }
                    Rule::binding_pattern => {
                        let name = pair_to_ast!(pat.into_inner().next().unwrap(), resolver)?;
                        Ok(ab.node(Pattern::Binding(name)))
                    }
                    Rule::ignore_pattern => Ok(ab.node(Pattern::Ignore)),
                    // @@Cleanup: is this right, can we avoid this by just using another AstNode here?
                    Rule::literal_pattern => {
                        Ok(ab.node(Pattern::Literal(*pair_to_ast!(pat, resolver)?.body)))
                    }
                    Rule::tuple_pattern => Ok(ab.node(Pattern::Tuple(TuplePattern {
                        elements: pairs_to_asts!(pat.into_inner(), resolver)?,
                    }))),

                    // grouped pattern is just a pattern surrounded by parenthesees, to specify precidence...
                    Rule::grouped_pattern => pair_to_ast!(pat, resolver),
                    k => panic!("unexpected rule within single_pattern: {:?}", k),
                }
            }
            Rule::compound_pattern => {
                let mut components = self.into_inner().into_inner();

                let pattern_rule = components.next().unwrap();
                let mut pats = pattern_rule.into_inner().map(|p| pair_to_ast!(p, resolver));

                let lhs = ab.node(Pattern::Or(OrPattern {
                    a: pats.next().unwrap()?,
                    b: pats.next().unwrap()?,
                }));

                Ok(match components.next() {
                    Some(k) => {
                        // the 'if' guared expects the rhs to be an expression
                        debug_assert_eq!(k.as_rule(), Rule::expr);

                        AstBuilder::from_pair(&k).node(Pattern::If(IfPattern {
                            pattern: lhs,
                            condition: pair_to_ast!(k, resolver)?,
                        }))
                    }
                    None => lhs,
                })
            }
            k => panic!("unexpected rule within expr: {:?}", k),
        }
    }
}

impl IntoAstNode<Expression> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<Expression>> {
        let ab = AstBuilder::from_pair(self.inner());

        match self.inner().as_rule() {
            Rule::fn_body => pair_to_ast!(self.into_inner().into_inner().next().unwrap(), resolver),
            Rule::expr => {
                let expr = self.into_inner().into_inner().next().unwrap();

                match expr.as_rule() {
                    Rule::block => Ok(ab.node(Expression::Block(pair_to_ast!(expr, resolver)?))),
                    Rule::struct_literal => {
                        Ok(ab.node(Expression::LiteralExpr(pair_to_ast!(expr, resolver)?)))
                    }
                    Rule::binary_expr => {
                        let mut items = expr.clone().into_inner();

                        // if this is an actual binary expr, we need to check if the second token is a
                        // binary_op and the invoke prec_climber.
                        let lhs = items.next().unwrap();

                        Ok(match items.next() {
                            Some(_) => climb(expr, resolver)?,
                            None => pair_to_ast!(lhs, resolver)?,
                        })
                    }
                    k => panic!("unexpected rule within inner_expr: {:?}", k),
                }
            }
            Rule::typed_expr => {
                let mut expr = self.into_inner().into_inner();

                // this is the unary expression...
                let unary = pair_to_ast!(expr.next().unwrap(), resolver)?;

                // check if this expression has a type...
                match expr.next() {
                    Some(ty) => Ok(ab.node(Expression::Typed(TypedExpr {
                        ty: pair_to_ast!(ty, resolver)?, // convert the type into an AstNode
                        expr: unary,
                    }))),
                    None => Ok(unary),
                }
            }
            Rule::unary_expr => {
                let mut expr = self.into_inner().into_inner();
                // check the first token to is if it is a unary expression, if so we
                // need convert this into the appropriate function call...
                let op_or_single_expr = expr.next().unwrap();

                match op_or_single_expr.as_rule() {
                    Rule::unary_op => {
                        let operator = op_or_single_expr.into_inner().next().unwrap();

                        let fn_call = String::from(match operator.as_rule() {
                            Rule::notb_op => "notb",
                            Rule::not_op => "not",
                            Rule::neg_op => "neg",
                            Rule::pos_op => "pos",
                            _ => unreachable!(),
                        });

                        // get the internal operand of the unary operator
                        let operand = expr.next().unwrap();

                        Ok(ab.node(Expression::FunctionCall(FunctionCallExpr {
                            subject: ab.node(Expression::Variable(VariableExpr {
                                name: ab.node(AccessName {
                                    names: vec![ab.node(Name { string: fn_call })],
                                }),
                                type_args: vec![],
                            })),
                            args: ab.node(FunctionCallArgs {
                                entries: vec![pair_to_ast!(operand, resolver)?],
                            }),
                        })))
                    }
                    _ => pair_to_ast!(op_or_single_expr, resolver),
                }
            }
            Rule::single_expr => {
                let mut expr = self.into_inner().into_inner();

                // a single expression is made of a 'subject' and then an accessor like a
                // an index, property_access or func args. So, we firstly convert the
                // subject into an ast_node and then deal with a potential 'accessor'...
                let subject_expr = expr.next().unwrap().into_inner().next().unwrap();
                let subject_rule = subject_expr.as_rule();

                let mut subject = match subject_rule {
                    Rule::intrinsic_expr => Ok(ab.node(Expression::Intrinsic(IntrinsicKey {
                        // @@Correctness: Currently, we preserve the '#' prefix for the intrinsic when
                        // working with the key, is this correct or should we throw away the '#'?
                        name: String::from(subject_expr.as_str()), // @@Redundant: Another uneccessary copy here??
                    }))),
                    Rule::import_expr => {
                        // we only care about the string literal here
                        let import_call = subject_expr.into_inner().next().unwrap();
                        let import_path = import_call.into_inner().next().unwrap();
                        let s = String::from(import_path.as_span().as_str());
                        let module_idx = resolver.add_module(&s, Some(ab.pos))?;

                        // get the string, but then convert into an AstNode using the string literal ast info
                        Ok(ab.node(Expression::Import(
                            AstBuilder::from_pair(&import_path).node(Import {
                                path: s,
                                index: module_idx,
                            }),
                        )))
                    }
                    Rule::literal_expr => Ok(ab.node(Expression::LiteralExpr(pair_to_ast!(
                        subject_expr,
                        resolver
                    )?))),
                    Rule::variable_expr => {
                        // so since this is going to be an access_name, which is a list of 'ident' rules,
                        // we can directly convert this into a VariableExpr
                        let mut var_expr = subject_expr.into_inner();

                        let access_name = var_expr.next().unwrap();

                        // is this even correct?
                        let names: Vec<AstNode<Name>> =
                            pairs_to_asts!(access_name.into_inner(), resolver)?;

                        // check for type args...
                        if let Some(ty) = var_expr.next() {
                            Ok(ab.node(Expression::Variable(VariableExpr {
                                name: ab.node(AccessName { names }),
                                type_args: pairs_to_asts!(ty.into_inner(), resolver)?,
                            })))
                        } else {
                            Ok(ab.node(Expression::Variable(VariableExpr {
                                name: ab.node(AccessName { names }),
                                type_args: vec![],
                            })))
                        }
                    }
                    Rule::paren_expr => pair_to_ast!(subject_expr, resolver),
                    k => panic!("unexpected rule within expr: {:?}", k),
                };

                // now let's check if there is an 'accessor' node with the subject. Since there
                // can be zero or more accessors, we need continue looking at each rule until there
                // are no more accessors. If there is an accessor, we pattern match for the type,
                // transform the old 'subject' and continue
                for accessor in expr {
                    let prev_subject = subject?;
                    subject = match accessor.as_rule() {
                        Rule::property_access => {
                            Ok(ab.node(Expression::PropertyAccess(PropertyAccessExpr {
                                subject: prev_subject,

                                // it's safe to unwrap here since property access will always
                                // provide the ident rule as the first one, otherwise it is a parsing error
                                property: pair_to_ast!(
                                    accessor.into_inner().next().unwrap(),
                                    resolver
                                )?,
                            })))
                        }
                        Rule::fn_args => {
                            // if it is func args, we need convert the 'subject' which is going
                            // to be a VariableExpr into a FunctionCallExpr
                            Ok(ab.node(Expression::FunctionCall(FunctionCallExpr {
                                subject: prev_subject,
                                args: AstBuilder::from_pair(&accessor).node(FunctionCallArgs {
                                    entries: pairs_to_asts!(accessor.into_inner(), resolver)?,
                                }),
                            })))
                        }
                        // we need to convert this into a 'index' function call on the
                        // current variable
                        Rule::index_arg => {
                            // if subject isn't a variable, how tf did we end up here
                            debug_assert_eq!(subject_rule, Rule::variable_expr);

                            // this is the expression within the brackets.
                            let index_expr =
                                pair_to_ast!(accessor.into_inner().next().unwrap(), resolver)?;

                            // @@Cutnpase: move this into a seprate function for transpilling built-in functions
                            Ok(ab.node(Expression::FunctionCall(FunctionCallExpr {
                                subject: ab.node(Expression::Variable(VariableExpr {
                                    name: ab.node(AccessName {
                                        names: vec![ab.node(Name {
                                            string: String::from("index"),
                                        })],
                                    }),
                                    type_args: vec![],
                                })),
                                args: ab.node(FunctionCallArgs {
                                    entries: vec![prev_subject, index_expr],
                                }),
                            })))
                        }
                        k => panic!("unexpected rule within variable expr: {:?}", k),
                    };
                }

                // since there can be zero or more 'accessor' rules, we are sure that the current
                // subject has been transformed as required, essentially nesting each form of
                // accessor in each other
                subject
            }
            k => panic!("unexpected rule within expr: {:?}", k),
        }
    }
}

impl IntoAstNode<Block> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<Block>> {
        let ab = AstBuilder::from_pair(&self.inner());

        match self.inner().as_rule() {
            Rule::block => {
                let block = self.into_inner().into_inner().next().unwrap();

                match block.as_rule() {
                    Rule::if_else_block => {
                        // we transpile if-else blocks into match blocks in order to simplify
                        // the typechecking process and optimisation effors.
                        // Firstly, since we always want to check each case, we convert the
                        // if statement into a series of and-patterns, where the right handside
                        // pattern is the condition to execute the branch...
                        //
                        // For example:
                        // >>> if a {a_branch} else if b {b_branch} else {c_branch}
                        // will be transpiled into...
                        // >>> match true {
                        //      _ if a => a_branch
                        //      _ if b => b_branch
                        //      _ => c_branch
                        //     }
                        //
                        // Adittionally, if no 'else' clause is specified, we fill it with an
                        // empty block since an if-block could be assigned to any variable and therefore
                        // we need to know the outcome of all branches for typechecking.
                        let mut append_else = true;
                        let mut cases: Vec<AstNode<MatchCase>> = block
                            .into_inner()
                            .map(|if_condition| {
                                let block_builder = AstBuilder::from_pair(&if_condition);

                                match if_condition.as_rule() {
                                    Rule::if_block => {
                                        let mut components = if_condition.into_inner();

                                        // get the clause and block from the if-block components
                                        let clause =
                                            pair_to_ast!(components.next().unwrap(), resolver)?;
                                        let block =
                                            pair_to_ast!(components.next().unwrap(), resolver)?;

                                        Ok(block_builder.node(MatchCase {
                                            pattern: block_builder.node(Pattern::If(IfPattern {
                                                pattern: block_builder.node(Pattern::Ignore),
                                                condition: clause,
                                            })),
                                            expr: AstBuilder::from_node(&block)
                                                .node(Expression::Block(block)),
                                        }))
                                    }
                                    Rule::else_block => {
                                        append_else = false;

                                        let block = pair_to_ast!(
                                            if_condition.into_inner().next().unwrap(),
                                            resolver
                                        )?;

                                        Ok(block_builder.node(MatchCase {
                                            pattern: block_builder.node(Pattern::Ignore),
                                            expr: AstBuilder::from_node(&block)
                                                .node(Expression::Block(block)),
                                        }))
                                    }
                                    k => panic!("unexpected rule within if-else-block: {:?}", k),
                                }
                            })
                            .collect::<Result<_, ParseError>>()?;

                        // if no else-block was provided, we need to add one manually
                        if append_else {
                            cases.push(ab.node(MatchCase {
                                pattern: ab.node(Pattern::Ignore),
                                expr: ab.node(Expression::Block(ab.node(Block::Body(BodyBlock {
                                    statements: vec![],
                                    expr: None,
                                })))),
                            }))
                        }

                        Ok(ab.node(Block::Match(MatchBlock {
                            subject: make_variable(make_boolean(true, &ab), &ab),
                            cases,
                        })))
                    }
                    Rule::match_block => {
                        let mut match_block = block.into_inner();

                        // firstly get the expresion condition from the match block, the
                        // next rule will be a bunch of match_case rules which can be
                        // converted into ast using the pattern and block implementations...
                        let subject = pair_to_ast!(match_block.next().unwrap(), resolver)?;
                        let match_cases = match_block.next().unwrap();

                        let cases = match_cases
                            .into_inner()
                            .map(|case| {
                                let case_builder = AstBuilder::from_pair(&case);

                                match case.as_rule() {
                                    Rule::match_case => {
                                        let mut components = case.into_inner();

                                        let pattern =
                                            pair_to_ast!(components.next().unwrap(), resolver)?;
                                        let expr =
                                            pair_to_ast!(components.next().unwrap(), resolver)?;

                                        Ok(case_builder.node(MatchCase { pattern, expr }))
                                    }
                                    k => panic!("unexpected rule within match_case: {:?}", k),
                                }
                            })
                            .collect::<Result<_, ParseError>>()?;

                        Ok(ab.node(Block::Match(MatchBlock { subject, cases })))
                    }
                    Rule::loop_block => {
                        let body_block =
                            pair_to_ast!(block.into_inner().next().unwrap(), resolver)?;

                        Ok(ab.node(Block::Loop(body_block)))
                    }
                    Rule::for_block => {
                        let mut for_block = block.into_inner();

                        let pattern: AstNode<Pattern> =
                            pair_to_ast!(for_block.next().unwrap(), resolver)?;
                        let pat_builder = AstBuilder::from_node(&pattern);

                        let iterator: AstNode<Expression> =
                            pair_to_ast!(for_block.next().unwrap(), resolver)?;
                        let iter_builder = AstBuilder::from_node(&iterator);

                        let body: AstNode<Block> =
                            pair_to_ast!(for_block.next().unwrap(), resolver)?;
                        let body_builder = AstBuilder::from_node(&body);

                        Ok(ab.node(Block::Loop(ab.node(Block::Match(MatchBlock {
                            subject: iter_builder.node(Expression::FunctionCall(
                                FunctionCallExpr {
                                    subject: iter_builder.node(Expression::Variable(
                                        VariableExpr {
                                            name: iter_builder.node(AccessName {
                                                names: vec![iter_builder.node(Name {
                                                    string: String::from("next"),
                                                })],
                                            }),
                                            type_args: vec![],
                                        },
                                    )),
                                    args: iter_builder.node(FunctionCallArgs {
                                        entries: vec![iterator],
                                    }),
                                },
                            )),
                            cases: vec![
                                body_builder.node(MatchCase {
                                    pattern: pat_builder.node(Pattern::Enum(EnumPattern {
                                        name: iter_builder.node(AccessName {
                                            names: vec![iter_builder.node(Name {
                                                string: String::from("Some"),
                                            })],
                                        }),
                                        args: vec![pattern],
                                    })),
                                    expr: body_builder.node(Expression::Block(body)),
                                }),
                                body_builder.node(MatchCase {
                                    pattern: pat_builder.node(Pattern::Enum(EnumPattern {
                                        name: iter_builder.node(AccessName {
                                            names: vec![iter_builder.node(Name {
                                                string: String::from("None"),
                                            })],
                                        }),
                                        args: vec![],
                                    })),
                                    expr: body_builder.node(Expression::Block(body_builder.node(
                                        Block::Body(BodyBlock {
                                            statements: vec![body_builder.node(Statement::Break)],
                                            expr: None,
                                        }),
                                    ))),
                                }),
                            ],
                        })))))
                    }
                    Rule::while_block => {
                        let mut while_block = block.into_inner();

                        let condition: AstNode<Expression> =
                            pair_to_ast!(while_block.next().unwrap(), resolver)?;
                        let condition_builder = AstBuilder::from_node(&condition);

                        let body: AstNode<Block> =
                            pair_to_ast!(while_block.next().unwrap(), resolver)?;
                        let body_builder = AstBuilder::from_node(&body);

                        Ok(ab.node(Block::Loop(ab.node(Block::Match(MatchBlock {
                            subject: condition,
                            cases: vec![
                                body_builder.node(MatchCase {
                                    pattern: condition_builder.node(Pattern::Enum(EnumPattern {
                                        name: make_boolean(true, &condition_builder),
                                        args: vec![],
                                    })),
                                    expr: body_builder.node(Expression::Block(body)),
                                }),
                                body_builder.node(MatchCase {
                                    pattern: condition_builder.node(Pattern::Enum(EnumPattern {
                                        name: make_boolean(false, &condition_builder),
                                        args: vec![],
                                    })),
                                    expr: body_builder.node(Expression::Block(body_builder.node(
                                        Block::Body(BodyBlock {
                                            statements: vec![body_builder.node(Statement::Break)],
                                            expr: None,
                                        }),
                                    ))),
                                }),
                            ],
                        })))))
                    }
                    Rule::body_block => Ok(pair_to_ast!(block, resolver)?),
                    k => panic!("unexpected rule within block variant: {:?}", k),
                }
            }
            Rule::body_block => {
                Ok(ab.node(Block::Body(BodyBlock {
                    statements: pairs_to_asts!(self.into_inner().into_inner(), resolver)?,
                    // @@FIXME: since the tokeniser cannot tell the difference betweeen a statment and an expression (what is returned), we need to do it here...
                    expr: None,
                })))
            }
            k => panic!("unexpected rule within block: {:?}", k),
        }
    }
}

impl IntoAstNode<Statement> for HashPair<'_> {
    fn into_ast(self, resolver: &mut impl ModuleResolver) -> ParseResult<AstNode<Statement>> {
        let ab = AstBuilder::from_pair(&self.inner());

        match self.inner().as_rule() {
            Rule::statement => {
                let statement = self.into_inner().into_inner().next().unwrap();

                // since we have block statements and semi statements, we can check here
                // to see which path it is, if this is a block statement, we just call
                // into_ast(resolver) since there is an implementation for block convetsions
                match statement.as_rule() {
                    Rule::block => {
                        Ok(ab.node(Statement::Block(pair_to_ast!(statement, resolver)?)))
                    }
                    Rule::break_st => Ok(ab.node(Statement::Break)),
                    Rule::continue_st => Ok(ab.node(Statement::Continue)),
                    Rule::return_st => {
                        let ret_expr = statement.into_inner().next();

                        if let Some(node) = ret_expr {
                            Ok(ab.node(Statement::Return(Some(pair_to_ast!(node, resolver)?))))
                        } else {
                            Ok(ab.node(Statement::Return(None)))
                        }
                    }
                    Rule::let_st => {
                        // the first rule will be the pattern which can be automatically converted, whereas
                        // then we have a trait bound and finally an optional expression which is used as an
                        // assignment to the let statement
                        let mut components = statement.into_inner();

                        let pattern = pair_to_ast!(components.next().unwrap(), resolver)?;

                        let bound_or_ty = components.next();
                        let (bound, ty, value) = match bound_or_ty {
                            Some(pair) => match pair.as_rule() {
                                Rule::bound => {
                                    let bound = Some(pair_to_ast!(pair, resolver)?);

                                    let ty_or_expr = components.next();

                                    match ty_or_expr {
                                        Some(r) => match r.as_rule() {
                                            Rule::any_type => (
                                                bound,
                                                Some(pair_to_ast!(r, resolver)?),
                                                // check if the optional value component is present with the let statement...
                                                components.next().map(|p| pair_to_ast!(p, resolver)).transpose()?,
                                            ),
                                            Rule::expr => {
                                                (bound, None, Some(pair_to_ast!(r, resolver)?))
                                            }
                                            k => {
                                                panic!("Unexpected rule within ty_or_expr: {:?}", k)
                                            }
                                        },
                                        None => (bound, None, None),
                                    }
                                }
                                Rule::any_type => (
                                    None,
                                    Some(pair_to_ast!(pair, resolver)?),
                                    components.next().map(|p| pair_to_ast!(p, resolver)).transpose()?,
                                ),
                                Rule::expr => (None, None, Some(pair_to_ast!(pair, resolver)?)),
                                k => panic!("Unexpected rule within let_st: {:?}", k),
                            },
                            None => (None, None, None),
                        };

                        Ok(ab.node(Statement::Let(LetStatement {
                            pattern,
                            ty,
                            bound,
                            value,
                        })))
                    }
                    Rule::expr_or_assign_st => {
                        let mut components = statement.into_inner();

                        // look at each kind of operator, since we need to perform some AST black magic, in
                        // the form of inserting a phantom node to represent the `lhs`. We have to do this because
                        // lhs expr might have side-effects included when it is evaluated and therefore we have to
                        // avoid from evalauting it twice...
                        //
                        // For example:
                        // >>> a[fn()] += 2;
                        //
                        // This looks pretty innocent at first glance, however what if 'fn()' which returns a
                        // valid integer slice also fires rockets as a side effect... we don't want to fire the rockets twice :^)
                        //
                        // So, what we have to do is insert a phantom ast_node which binds the lhs to
                        // '$index', so that it can be used when transpilling the re-assignment operators...
                        let lhs: AstNode<Expression> =
                            pair_to_ast!(components.next().unwrap(), resolver)?;

                        // if no rhs is present, this is just an singular expression instead of an
                        // assignment
                        match components.next() {
                            Some(op_wrap) => {
                                // get the assignment operator out of 'assign_op'
                                let op = op_wrap.into_inner().next().unwrap();
                                let transform = convert_rule_into_fn_call(&op.as_rule());

                                let mut rhs = pair_to_ast!(components.next().unwrap(), resolver)?;

                                // transform lhs if we're using a non-eq assignment operator into the appropriate
                                // function call...
                                if let Some(fn_name) = transform {
                                    // Representing '$internal' as an identifier
                                    let builder = AstBuilder::from_node(&rhs);
                                    let internal_node = make_internal_node(&builder);

                                    let internal_decl = AstBuilder::from_node(&lhs).node(
                                        Statement::Assign(AssignStatement {
                                            lhs: internal_node.clone(),
                                            rhs: lhs.clone(),
                                        }),
                                    );

                                    // transform the right hand side into the appropriate expression, by representing the
                                    // modification operator into a function call and then setting the lhs and rhs as
                                    // arguments to the function call. So, essentially the expression `lhs += rhs` is transformed
                                    // into `lhs = lhs + rhs`
                                    rhs =
                                        builder.node(Expression::FunctionCall(FunctionCallExpr {
                                            subject: builder.node(Expression::Variable(
                                                VariableExpr {
                                                    name: builder.node(AccessName {
                                                        names: vec![
                                                            builder.node(Name { string: fn_name })
                                                        ],
                                                    }),
                                                    type_args: vec![],
                                                },
                                            )),
                                            args: AstBuilder::from_node(&rhs).node(
                                                FunctionCallArgs {
                                                    entries: vec![internal_node.clone(), rhs],
                                                },
                                            ),
                                        }));

                                    // make the assignment
                                    let assignment = ab.node(Statement::Assign(AssignStatement {
                                        lhs: internal_node.clone(),
                                        rhs,
                                    }));

                                    // a[side_effect] += 2
                                    //
                                    // transforms into...
                                    // {
                                    //  $internal = a[side_effect]
                                    //  $internal = $internal + 2
                                    //  $internal
                                    // }
                                    //
                                    return Ok(ab.node(Statement::Expr(builder.node(
                                        Expression::Block(builder.node(Block::Body(BodyBlock {
                                            statements: vec![internal_decl, assignment],
                                            expr: Some(internal_node), // the return statement is just the internal node
                                        }))),
                                    ))));
                                }

                                Ok(ab.node(Statement::Assign(AssignStatement { lhs, rhs })))
                            }
                            None => Ok(ab.node(Statement::Expr(lhs))),
                        }
                    }
                    Rule::struct_def => {
                        let mut components = statement.into_inner();
                        let name = pair_to_ast!(components.next().unwrap(), resolver)?;

                        let bound_or_fields = components.next().unwrap();
                        let (bound, entries) = match bound_or_fields.as_rule() {
                            Rule::bound => (
                                Some(pair_to_ast!(bound_or_fields, resolver)?),
                                // It's guaranteed to have zero or more struct def fields and so it is
                                // safe to unwrap the following rule after the bound...
                                pairs_to_asts!(components.next().unwrap().into_inner(), resolver)?,
                            ),

                            Rule::struct_def_fields => (
                                None,
                                pairs_to_asts!(bound_or_fields.into_inner(), resolver)?,
                            ),
                            k => panic!("Unexpected rule within struct_def: {:?}", k),
                        };
                        Ok(ab.node(Statement::StructDef(StructDef {
                            name,
                            bound,
                            entries,
                        })))
                    }
                    Rule::enum_def => {
                        let mut components = statement.into_inner();
                        let name = pair_to_ast!(components.next().unwrap(), resolver)?;

                        let bound_or_fields = components.next().unwrap();
                        let (bound, entries) = match bound_or_fields.as_rule() {
                            Rule::bound => (
                                Some(pair_to_ast!(bound_or_fields, resolver)?),
                                pairs_to_asts!(components.next().unwrap().into_inner(), resolver)?,
                            ),
                            // It's guaranteed to have zero or more enum def fields and so it is
                            // safe to unwrap the following rule after the bound...
                            Rule::enum_fields => (
                                None,
                                pairs_to_asts!(bound_or_fields.into_inner(), resolver)?,
                            ),
                            k => panic!("Unexpected rule within enum_def: {:?}", k),
                        };

                        Ok(ab.node(Statement::EnumDef(EnumDef {
                            name,
                            bound,
                            entries,
                        })))
                    }
                    Rule::trait_def => {
                        let mut components = statement.into_inner();
                        let name = pair_to_ast!(components.next().unwrap(), resolver)?;
                        let bound = pair_to_ast!(components.next().unwrap(), resolver)?;

                        // @@Incomplete: ensure that this is a function_type!!
                        let trait_type = pair_to_ast!(components.next().unwrap(), resolver)?;

                        Ok(ab.node(Statement::TraitDef(TraitDef {
                            name,
                            bound,
                            trait_type,
                        })))
                    }
                    _ => unreachable!(),
                }
            }
            // This rule must be present here because body_block's are made of a
            // arbitrary number of statements, and an optional final expression.
            // So, when we convert the body_blocks' into ast, we don't know if the
            // last item is a statement or expression...
            Rule::expr => Ok(ab.node(Statement::Expr(pair_to_ast!(self.into_inner(), resolver)?))),
            k => panic!("unexpected rule within statement: {:?}", k),
        }
    }
}

#[cfg(test)]
mod tests {
    // use pest::Parser;

    // use super::*;

    // fn parse_input<T>(rule: Rule, input: &str) -> AstNode<T>
    // where
    //     for<'a> HashPair<'a>: IntoAstNode<T>,
    // {
    //     let resolver = SeqModuleResolver::new();
    //     let mut result = grammar::HashGrammar::parse(rule, input).unwrap();
    //     let parsed: AstNode<T> = result.next().unwrap().into_ast(&resolver);
    //     parsed
    // }

    // #[test]
    // fn test_name() {
    //     assert_eq!(
    //         AstNode {
    //             body: Box::new(Name {
    //                 string: "universe".to_owned()
    //             }),
    //             pos: Location::Span(0, 8,),
    //             module: 0,
    //         },
    //         parse_input::<Name>(Rule::name, "universe"),
    //     );
    // }

    // #[test]
    // fn test_access_name() {
    //     assert_eq!(
    //         AstNode {
    //             body: Box::new(AccessName {
    //                 names: vec![
    //                     AstNode {
    //                         body: Box::new(Name {
    //                             string: "iter".to_owned()
    //                         }),
    //                         pos: Location::Span(0, 4,),
    //                         module: 0,
    //                     },
    //                     AstNode {
    //                         body: Box::new(Name {
    //                             string: "next".to_owned()
    //                         }),
    //                         pos: Location::Span(6, 10,),
    //                         module: 0,
    //                     },
    //                     AstNode {
    //                         body: Box::new(Name {
    //                             string: "Then".to_owned()
    //                         }),
    //                         pos: Location::Span(12, 16,),
    //                         module: 0,
    //                     },
    //                 ],
    //             }),
    //             pos: Location::Span(0, 16,),
    //             module: 0,
    //         },
    //         parse_input::<AccessName>(Rule::access_name, "iter::next::Then"),
    //     );
    // }
}
