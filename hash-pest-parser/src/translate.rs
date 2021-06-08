//! Hash compiler module for converting from tokens to an AST tree
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::{cell::Cell, iter};

use crate::{
    grammar::{HashPair, Rule},
    precedence::PREC_CLIMBER,
    utils::convert_rule_into_fn_call,
};
use hash_ast::{
    ast::*,
    error::{ParseError, ParseResult},
    location::Location,
    parse::ModuleResolver,
};
use iter::once;
use num::BigInt;

const FUNCTION_TYPE_NAME: &str = "Function";
const TUPLE_TYPE_NAME: &str = "Tuple";
const LIST_TYPE_NAME: &str = "List";
const SET_TYPE_NAME: &str = "Set";
const MAP_TYPE_NAME: &str = "Map";

/// A wrapper around AstNode to build [AstNode]s with the same information as the builder
/// holds. Creating new [AstNode]s with the the builder will copy over the [ModuleIndex]
/// and the [Location] of the node. An [AstBuilder] can be created from an existing node,
/// or a [pest::iterators::Pair].
pub struct NodeBuilder<'alloc, A> {
    pos: Location,
    allocator: &'alloc A,
}

impl<'ast, 'alloc, A> NodeBuilder<'alloc, A>
where
    A: AstAllocator<'ast, 'alloc>,
    'ast: 'alloc,
{
    pub(crate) fn from_pair(pair: &HashPair<'_>, allocator: &'alloc A) -> NodeBuilder<'alloc, A> {
        let span = pair.as_span();
        let pos = Location::span(span.start(), span.end());
        NodeBuilder { pos, allocator }
    }

    pub(crate) fn from_node<T>(
        node: &AstNode<'ast, T>,
        allocator: &'alloc A,
    ) -> NodeBuilder<'alloc, A> {
        NodeBuilder {
            pos: node.pos,
            allocator,
        }
    }

    /// Create a new [AstNode] from the information provided by the [AstBuilder]
    pub fn node<T>(&self, inner: T) -> AstNode<'ast, T> {
        self.allocator.alloc_ast_node(inner, self.pos)
    }

    /// Create a new [AstNode] from the information provided by the [AstBuilder]
    pub fn existing_node<T>(&self, inner: &'ast mut T) -> AstNode<'ast, T> {
        AstNode {
            body: inner,
            pos: self.pos,
        }
    }

    pub fn error(&self, message: String) -> ParseError {
        ParseError::AstGeneration {
            location: self.pos,
            message,
        }
    }

    fn try_collect<T, I>(&self, iter: I) -> Result<&'ast mut [T], ParseError>
    where
        I: Iterator<Item = Result<T, ParseError>>,
    {
        self.allocator.try_alloc_slice(iter)
    }

    fn empty_slice<T>(&self) -> &'ast mut [T] {
        self.allocator.alloc([])
    }

    fn make_single_access_name(&self, name: &str) -> AstNode<'ast, AccessName<'ast>> {
        self.node(AccessName {
            names: self.allocator.alloc([self.node(Name {
                string: self.allocator.alloc_str(name),
            })]),
        })
    }

    fn make_name(&self, name: &str) -> AstNode<'ast, Name<'ast>> {
        self.node(Name {
            string: self.allocator.alloc_str(name),
        })
    }

    fn copy_name_node(&self, name: &AstNode<Name>) -> AstNode<'ast, Name<'ast>> {
        self.node(Name {
            string: self.allocator.alloc_str(name.body.string),
        })
    }

    /// Utility for creating a boolean in enum representation
    fn make_boolean(&self, variant: bool) -> AstNode<'ast, AccessName<'ast>> {
        let name_ref = match variant {
            false => "false",
            true => "true",
        };

        self.node(AccessName {
            names: self.allocator.alloc([self.node(Name {
                string: self.allocator.alloc_str(name_ref),
            })]),
        })
    }

    /// Utility finction for creating a variable from a given name.
    fn make_variable(
        &self,
        name: AstNode<'ast, AccessName<'ast>>,
    ) -> AstNode<'ast, Expression<'ast>> {
        self.node(Expression::Variable(VariableExpr {
            name,
            type_args: self.empty_slice(),
        }))
    }

    /// Utility function to make an `$internal` identifier reference, this is used when
    /// transforming assignment with update operators like `+=`
    fn make_internal_node(&self) -> AstNode<'ast, Expression<'ast>> {
        self.node(Expression::Variable(VariableExpr {
            name: self.node(AccessName {
                names: self.allocator.alloc([self.node(Name {
                    string: self.allocator.alloc_str("$internal"),
                })]),
            }),
            type_args: self.empty_slice(),
        }))
    }
}

pub(crate) fn build_binary<'ast: 'alloc, 'alloc, A>(
    lhs: ParseResult<AstNode<'ast, Expression<'ast>>>,
    op: HashPair<'_>,
    rhs: ParseResult<AstNode<'ast, Expression<'ast>>>,
    allocator: &'alloc A,
) -> ParseResult<AstNode<'ast, Expression<'ast>>>
where
    A: AstAllocator<'ast, 'alloc>,
{
    let ab = NodeBuilder::from_pair(&op, allocator);

    // Panic here if we cannot convert the operator into a function call
    let subject_name = convert_rule_into_fn_call(&op.as_rule()).unwrap();

    Ok(ab.node(Expression::FunctionCall(FunctionCallExpr {
        subject: ab.node(Expression::Variable(VariableExpr {
            name: ab.make_single_access_name(subject_name),
            type_args: ab.empty_slice(), // we dont need any kind of typeargs since were just transpiling here
        })),
        args: ab.node(FunctionCallArgs {
            entries: allocator.alloc([lhs?, rhs?]),
        }),
    })))
}

pub(crate) struct PestAstBuilder<'alloc, 'resolver, R, A> {
    resolver: &'resolver mut R,
    allocator: &'alloc A,
}

impl<'ast, 'alloc, 'resolver, R, A> PestAstBuilder<'alloc, 'resolver, R, A>
where
    R: ModuleResolver,
    A: AstAllocator<'ast, 'alloc>,
    'ast: 'alloc,
{
    pub(crate) fn new(resolver: &'resolver mut R, allocator: &'alloc A) -> Self {
        Self {
            resolver,
            allocator,
        }
    }

    pub(crate) fn builder_from_pair(&self, pair: &HashPair<'_>) -> NodeBuilder<'alloc, A> {
        NodeBuilder::from_pair(pair, self.allocator)
    }

    pub(crate) fn builder_from_node<T>(&self, node: &AstNode<'ast, T>) -> NodeBuilder<'alloc, A> {
        NodeBuilder::from_node(node, self.allocator)
    }

    pub(crate) fn climb<'i, P>(&mut self, pairs: P) -> ParseResult<AstNode<'ast, Expression<'ast>>>
    where
        P: Iterator<Item = HashPair<'i>>,
    {
        let allocator = self.allocator;
        PREC_CLIMBER.climb(
            pairs,
            |pair| self.transform_expression(pair),
            |lhs, op, rhs| build_binary(lhs, op, rhs, allocator),
        )
    }

    pub(crate) fn transform_name(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, Name<'ast>>> {
        match pair.as_rule() {
            Rule::ident => Ok(self.builder_from_pair(&pair).node(Name {
                string: self.allocator.alloc_str(pair.as_str()),
            })),
            _ => unreachable!(),
        }
    }

    pub(crate) fn transform_struct_def_entry(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, StructDefEntry<'ast>>> {
        match pair.as_rule() {
            Rule::struct_def_field => {
                let ab = self.builder_from_pair(&pair);
                let mut components = pair.into_inner();

                let name = self.transform_name(components.next().unwrap())?;
                let next_node = components.next();

                let (ty, def) = match next_node {
                    Some(inner_pair) => match inner_pair.as_rule() {
                        Rule::any_type => (
                            Some(self.transform_type(inner_pair)?),
                            components
                                .next()
                                .map(|p| self.transform_expression(p))
                                .transpose()?,
                        ),
                        Rule::expr => (None, Some(self.transform_expression(inner_pair)?)),
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

    pub(crate) fn transform_struct_literal_entry(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, StructLiteralEntry<'ast>>> {
        match pair.as_rule() {
            Rule::struct_literal_field => {
                let ab = self.builder_from_pair(&pair);
                let mut components = pair.into_inner();

                let name = self.transform_name(components.next().unwrap())?;
                let value = self.transform_expression(components.next().unwrap())?;

                Ok(ab.node(StructLiteralEntry { name, value }))
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn transform_enum_def_entry(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, EnumDefEntry<'ast>>> {
        match pair.as_rule() {
            Rule::enum_field => {
                let ab = self.builder_from_pair(&pair);
                let mut components = pair.into_inner();

                let name = self.transform_name(components.next().unwrap())?;
                let args = ab.try_collect(components.map(|c| self.transform_type(c)))?;

                Ok(ab.node(EnumDefEntry { name, args }))
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn transform_bound(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, Bound<'ast>>> {
        match pair.as_rule() {
            Rule::bound => {
                let ab = self.builder_from_pair(&pair);
                let mut components = pair.into_inner();

                // firsly convertkk the type args by just iterating the inner component
                // of the type_args rule...
                let type_args = ab.try_collect(
                    components
                        .next()
                        .unwrap()
                        .into_inner()
                        .map(|x| self.transform_type(x)),
                )?;

                // check if there are any trait_bounds attached with this bound
                let trait_bounds = match components.next() {
                    Some(pair) => {
                        ab.try_collect(pair.into_inner().map(|x| self.transform_trait_bound(x)))?
                    }
                    None => ab.empty_slice(),
                };

                Ok(ab.node(Bound {
                    type_args,
                    trait_bounds,
                }))
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn transform_trait_bound(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, TraitBound<'ast>>> {
        match pair.as_rule() {
            Rule::trait_bound => {
                let ab = self.builder_from_pair(&pair);
                let mut components = pair.into_inner();

                // convert the access_name rule into a AstNode, each trait bound is guaranteed
                // to have an access name, so it's safe to unwrap here...
                let name = self.transform_access_name(components.next().unwrap())?;

                // convert any type args the trait bound contains
                let type_args = match components.next() {
                    Some(pair) => {
                        ab.try_collect(pair.into_inner().map(|x| self.transform_type(x)))?
                    }
                    None => ab.empty_slice(),
                };

                Ok(ab.node(TraitBound { name, type_args }))
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn transform_access_name(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, AccessName<'ast>>> {
        let ab = self.builder_from_pair(&pair);
        match pair.as_rule() {
            Rule::access_name => Ok(self.builder_from_pair(&pair).node(AccessName {
                names: ab.try_collect(pair.into_inner().map(|x| self.transform_name(x)))?,
            })),
            _ => unreachable!(),
        }
    }

    pub(crate) fn transform_type(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, Type<'ast>>> {
        let ab = self.builder_from_pair(&pair);

        match pair.as_rule() {
            Rule::any_type => {
                let in_type = pair.into_inner().next().unwrap();
                self.transform_type(in_type)
            }
            Rule::infer_type => Ok(ab.node(Type::Infer)),
            Rule::named_type => {
                let mut in_named = pair.into_inner();

                let name = self.transform_access_name(in_named.next().unwrap())?;
                let type_args = in_named
                    .next()
                    .map(|n| ab.try_collect(n.into_inner().map(|x| self.transform_type(x))))
                    .unwrap_or_else(|| Ok(ab.empty_slice()))?;

                Ok(ab.node(Type::Named(NamedType { name, type_args })))
            }
            Rule::fn_type => {
                let mut in_func = pair.into_inner();

                let func_args = in_func.next().unwrap();
                let func_return_ty = self.transform_type(in_func.next().unwrap());

                let type_args = ab.try_collect(
                    func_args
                        .into_inner()
                        .map(|x| self.transform_type(x))
                        .chain(once(func_return_ty)),
                )?;

                Ok(ab.node(Type::Named(NamedType {
                    name: ab.make_single_access_name(FUNCTION_TYPE_NAME),
                    type_args,
                })))
            }
            Rule::tuple_type => {
                let inner = ab.try_collect(pair.into_inner().map(|x| self.transform_type(x)))?;
                Ok(ab.node(Type::Named(NamedType {
                    name: ab.make_single_access_name(TUPLE_TYPE_NAME),
                    type_args: inner,
                })))
            }
            Rule::list_type => {
                let inner = ab.try_collect(pair.into_inner().map(|x| self.transform_type(x)))?;

                // list type should only have one type
                debug_assert_eq!(inner.len(), 1);

                Ok(ab.node(Type::Named(NamedType {
                    name: ab.make_single_access_name(LIST_TYPE_NAME),
                    type_args: inner,
                })))
            }
            Rule::set_type => {
                let inner = ab.try_collect(pair.into_inner().map(|x| self.transform_type(x)))?;

                // set type should only have one type
                debug_assert_eq!(inner.len(), 1);

                Ok(ab.node(Type::Named(NamedType {
                    name: ab.make_single_access_name(SET_TYPE_NAME),
                    type_args: inner,
                })))
            }
            Rule::map_type => {
                let inner = ab.try_collect(pair.into_inner().map(|x| self.transform_type(x)))?;

                // map type should only have a type for a key and a value
                debug_assert_eq!(inner.len(), 2);

                Ok(ab.node(Type::Named(NamedType {
                    name: ab.make_single_access_name(MAP_TYPE_NAME),
                    type_args: inner,
                })))
            }
            Rule::existential_type => Ok(ab.node(Type::Existential)),
            k => panic!("unexpected rule within type: {:?} at {:?}", k, pair),
        }
    }

    pub(crate) fn transform_literal(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, Literal<'ast>>> {
        let ab = self.builder_from_pair(&pair);

        match pair.as_rule() {
            // If the literal is wrapped in a literal_expr, we unwrap it and then just convert
            // the internal contents of it using the same implementation...
            Rule::literal_expr => self.transform_literal(pair.into_inner().next().unwrap()),
            Rule::integer_literal => {
                let inner = pair.into_inner().next().unwrap();
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
                let mut components = pair.into_inner();

                // float_literal is made of three parts, the integer part, fractical part
                // and an optional exponent part...
                let float = components.next().unwrap();

                let value: f64 = float
                    .as_str()
                    .parse()
                    .map_err(|_| ab.error("Invalid float literal.".to_owned()))?;

                // apply exponent if any
                let exp_value = match components.next() {
                    Some(pair) => {
                        // since it might also have a -/+ sign, we need join it with the exponent int literal...
                        //
                        // Dumbass pest doesn't produce the right result when just calling
                        // pair.as_ast()...
                        let str_val = pair.into_inner().map(|p| p.as_str()).collect::<String>();

                        let exponent: i32 = str_val.parse().map_err(|_| {
                            ab.error(format!("Invalid float exponent: {}", str_val))
                        })?;

                        value.powi(exponent)
                    }
                    None => value,
                };

                Ok(ab.node(Literal::Float(exp_value)))
            }
            Rule::char_literal => {
                // we need to get the second character in the literal because the first one will be the character quote, since pest includes them in the span
                let c: char = pair.as_str().chars().nth(1).unwrap();
                Ok(ab.node(Literal::Char(c)))
            }
            Rule::string_literal => {
                let s = pair.into_inner().next().unwrap().as_str();
                Ok(ab.node(Literal::Str(self.allocator.alloc_str(s))))
            }
            Rule::list_literal => {
                // since list literals are just a bunch of expressions, we just call
                // into_ast(resolver) on each member and collect at the end
                let elements =
                    ab.try_collect(pair.into_inner().map(|x| self.transform_expression(x)))?;

                Ok(ab.node(Literal::List(ListLiteral { elements })))
            }
            Rule::set_literal => {
                // since set literals are just a bunch of expressions, we just call
                // into_ast(resolver) on each member and collect at the end
                let elements =
                    ab.try_collect(pair.into_inner().map(|x| self.transform_expression(x)))?;

                Ok(ab.node(Literal::Set(SetLiteral { elements })))
            }
            Rule::tuple_literal => {
                // since tuple literals are just a bunch of expressions, we just call
                // into_ast(resolver) on each member and collect at the end
                let elements =
                    ab.try_collect(pair.into_inner().map(|x| self.transform_expression(x)))?;

                Ok(ab.node(Literal::Tuple(TupleLiteral { elements })))
            }
            Rule::map_literal => {
                // A map is made of a vector of 'map_entries' rules, which are just two
                // expressions.
                let elements = ab.try_collect(pair.into_inner().map(|p| {
                    let mut items = p.into_inner().map(|p| self.transform_expression(p));
                    Ok((items.next().unwrap()?, items.next().unwrap()?))
                }))?;

                Ok(ab.node(Literal::Map(MapLiteral { elements })))
            }
            Rule::fn_literal => {
                // we're looking for a number of function arguments, an optional return and
                // a function body which is just an expression.
                let mut components = pair.into_inner();

                // firstly, take care of the function parameters...
                let args =
                    ab.try_collect(components.next().unwrap().into_inner().map(|param| {
                        let mut param_components = param.into_inner();

                        // get the name of identifier
                        let name = self.transform_name(param_components.next().unwrap())?;

                        // if no type is specified for the param, we just set it to none
                        let ty = param_components
                            .next()
                            .map(|t| self.transform_type(t))
                            .transpose()?;

                        Ok(ab.node(FunctionDefArg { name, ty }))
                    }))?;

                // now check here if the next rule is either a type or a expression,
                // if it is a type, we expect that there are two more rules to follow
                // since function literals cannot be without a fn_body
                let fn_type_or_body = components.next().unwrap();

                let (return_ty, fn_body) = match fn_type_or_body.as_rule() {
                    Rule::any_type => {
                        let body = components.next().unwrap();
                        (
                            Some(self.transform_type(fn_type_or_body)?),
                            self.transform_expression(body)?,
                        )
                    }
                    Rule::fn_body => (None, self.transform_expression(fn_type_or_body)?),
                    k => panic!("unexpected rule within fn_literal: {:?}", k),
                };
                Ok(ab.node(Literal::Function(FunctionDef {
                    args,
                    return_ty,
                    fn_body,
                })))
            }
            Rule::struct_literal => {
                let mut components = pair.into_inner();

                // first sort out the name of the struct
                let name = self.transform_access_name(components.next().unwrap())?;

                // now check if the next rule is either type_args or struct_fields...
                let type_args_or_fields = components.next().unwrap();

                let (type_args, entries) = match type_args_or_fields.as_rule() {
                    Rule::type_args => {
                        // convert the type args into ast nodes...
                        let type_args = ab.try_collect(
                            type_args_or_fields
                                .into_inner()
                                .map(|x| self.transform_type(x)),
                        )?;

                        // convert the struct fields into ast nodes...
                        let fields = ab.try_collect(
                            components
                                .next()
                                .unwrap()
                                .into_inner()
                                .map(|x| self.transform_struct_literal_entry(x)),
                        )?;

                        (type_args, fields)
                    }
                    Rule::struct_literal_fields => (
                        ab.empty_slice(),
                        ab.try_collect(
                            type_args_or_fields
                                .into_inner()
                                .map(|x| self.transform_struct_literal_entry(x)),
                        )?,
                    ),
                    k => panic!("unexpected rule within struct_literal: {:?}", k),
                };

                Ok(ab.node(Literal::Struct(StructLiteral {
                    name,
                    type_args,
                    entries,
                })))
            }
            k => panic!("unexpected rule within literal: {:?} at {:?}", k, pair),
        }
    }

    pub(crate) fn transform_literal_pattern(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<LiteralPattern<'ast>> {
        match pair.as_rule() {
            Rule::literal_pattern => {
                let pat = pair.into_inner().next().unwrap();

                // we prematurely convert the first node into a Literal, and then
                // pattern match on the literal, converting into a Literal pattern
                let node = self.transform_literal(pat)?;

                // essentially cast the literal into a literal_pattern
                Ok(match node.body {
                    Literal::Str(s) => LiteralPattern::Str(s),
                    Literal::Char(s) => LiteralPattern::Char(*s),
                    Literal::Float(s) => LiteralPattern::Float(*s),
                    Literal::Int(s) => LiteralPattern::Int(s.clone()),
                    k => panic!(
                        "literal_pattern should be string, float, char or int, got : {:?}",
                        k
                    ),
                })
            }
            k => panic!("unexpected rule within literal_pattern: {:?}", k),
        }
    }

    pub(crate) fn transform_pattern(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, Pattern<'ast>>> {
        let ab = self.builder_from_pair(&pair);

        match pair.as_rule() {
            Rule::pattern => self.transform_pattern(pair.into_inner().next().unwrap()),
            Rule::single_pattern => {
                let pat = pair.into_inner().next().unwrap();

                match pat.as_rule() {
                    Rule::enum_pattern => {
                        let mut components = pat.into_inner();

                        let name = self.transform_access_name(components.next().unwrap())?;
                        let args = ab.try_collect(
                            components
                                .next()
                                .unwrap()
                                .into_inner()
                                .map(|x| self.transform_pattern(x)),
                        )?;

                        Ok(ab.node(Pattern::Enum(EnumPattern { name, args })))
                    }
                    Rule::struct_pattern => {
                        let mut components = pat.into_inner();

                        let name = self.transform_access_name(components.next().unwrap())?;

                        // If there is no binding part of the destructuring pattern, as in if
                        // no pattern on the right-handside, we use the name of the field as a
                        // binding pattern here...
                        let entries =
                            ab.try_collect(components.next().unwrap().into_inner().map(|p| {
                                let mut field = p.into_inner();
                                let name = self.transform_name(field.next().unwrap())?;
                                let name_ab = self.builder_from_node(&name);

                                let pattern = match field.next() {
                                    Some(pat) => self.transform_pattern(pat)?,
                                    None => name_ab
                                        .node(Pattern::Binding(name_ab.copy_name_node(&name))),
                                };

                                Ok(name_ab.node(DestructuringPattern { name, pattern }))
                            }))?;

                        Ok(ab.node(Pattern::Struct(StructPattern { name, entries })))
                    }
                    Rule::namespace_pattern => {
                        let patterns = ab.try_collect(pat.into_inner().map(|p| {
                            let mut field = p.into_inner();
                            let name = self.transform_name(field.next().unwrap())?;
                            let name_ab = self.builder_from_node(&name);

                            let pattern = match field.next() {
                                Some(pat) => self.transform_pattern(pat)?,
                                None => {
                                    name_ab.node(Pattern::Binding(name_ab.copy_name_node(&name)))
                                }
                            };

                            Ok(name_ab.node(DestructuringPattern { name, pattern }))
                        }))?;

                        Ok(ab.node(Pattern::Namespace(NamespacePattern { patterns })))
                    }
                    Rule::binding_pattern => {
                        let name = self.transform_name(pat.into_inner().next().unwrap())?;
                        Ok(ab.node(Pattern::Binding(name)))
                    }
                    Rule::ignore_pattern => Ok(ab.node(Pattern::Ignore)),
                    // @@Cleanup: is this right, can we avoid this by just using another AstNode here?
                    Rule::literal_pattern => {
                        let literal = self.transform_literal_pattern(pat)?;
                        Ok(ab.node(Pattern::Literal(literal)))
                    }
                    Rule::tuple_pattern => Ok(ab.node(Pattern::Tuple(TuplePattern {
                        elements: ab
                            .try_collect(pat.into_inner().map(|x| self.transform_pattern(x)))?,
                    }))),

                    // grouped pattern is just a pattern surrounded by parentheses, to specify precedence...
                    Rule::grouped_pattern => self.transform_pattern(pat),
                    k => panic!("unexpected rule within single_pattern: {:?}", k),
                }
            }
            Rule::compound_pattern => {
                let mut components = pair.into_inner();

                let pattern_rule = components.next().unwrap();
                let mut pats = pattern_rule.into_inner().map(|p| self.transform_pattern(p));

                let lhs = ab.node(Pattern::Or(OrPattern {
                    a: pats.next().unwrap()?,
                    b: pats.next().unwrap()?,
                }));

                Ok(match components.next() {
                    Some(k) => {
                        // the 'if' guared expects the rhs to be an expression
                        debug_assert_eq!(k.as_rule(), Rule::expr);

                        self.builder_from_pair(&k).node(Pattern::If(IfPattern {
                            pattern: lhs,
                            condition: self.transform_expression(k)?,
                        }))
                    }
                    None => lhs,
                })
            }
            k => panic!("unexpected rule within expr: {:?}", k),
        }
    }

    pub(crate) fn transform_expression<'s>(
        &mut self,
        pair: HashPair<'s>,
    ) -> ParseResult<AstNode<'ast, Expression<'ast>>> {
        let ab = self.builder_from_pair(&pair);
        let rule = pair.as_rule();
        let mut expr = pair.into_inner();

        match rule {
            Rule::fn_body => self.transform_expression(expr.next().unwrap()),
            Rule::expr => {
                let expr = expr.next().unwrap();

                match expr.as_rule() {
                    Rule::block => Ok(ab.node(Expression::Block(self.transform_block(expr)?))),
                    Rule::struct_literal => {
                        Ok(ab.node(Expression::LiteralExpr(self.transform_literal(expr)?)))
                    }
                    Rule::binary_expr => {
                        let mut items = expr.into_inner();

                        // if this is an actual binary expr, we need to check if the second token is a
                        // binary_op and the invoke prec_climber.
                        let lhs = items.next().unwrap();

                        Ok(match items.next() {
                            Some(op) => self.climb(once(lhs).chain(once(op)).chain(items))?,
                            None => self.transform_expression(lhs)?,
                        })
                    }
                    k => panic!("unexpected rule within inner_expr: {:?}", k),
                }
            }
            Rule::typed_expr => {
                // this is the unary expression...
                let unary = self.transform_expression(expr.next().unwrap())?;

                // check if this expression has a type...
                match expr.next() {
                    Some(ty) => Ok(ab.node(Expression::Typed(TypedExpr {
                        ty: self.transform_type(ty)?, // convert the type into an AstNode
                        expr: unary,
                    }))),
                    None => Ok(unary),
                }
            }
            Rule::unary_expr => {
                // check the first token to is if it is a unary expression, if so we
                // need convert this into the appropriate function call...
                let op_or_single_expr = expr.next().unwrap();

                match op_or_single_expr.as_rule() {
                    Rule::unary_op => {
                        let operator = op_or_single_expr.into_inner().next().unwrap();

                        let fn_call = match operator.as_rule() {
                            Rule::notb_op => "notb",
                            Rule::not_op => "not",
                            Rule::neg_op => "neg",
                            Rule::pos_op => "pos",
                            _ => unreachable!(),
                        };

                        // get the internal operand of the unary operator
                        let operand = expr.next().unwrap();

                        Ok(ab.node(Expression::FunctionCall(FunctionCallExpr {
                            subject: ab.node(Expression::Variable(VariableExpr {
                                name: ab.make_single_access_name(fn_call),
                                // name: ab.node(AccessName {
                                //     names: self.allocator.alloc([inab.node(Name { string:  })]),
                                // }),
                                type_args: ab.empty_slice(),
                            })),
                            args: ab.node(FunctionCallArgs {
                                entries: self
                                    .allocator
                                    .alloc([self.transform_expression(operand)?]),
                            }),
                        })))
                    }
                    _ => self.transform_expression(op_or_single_expr),
                }
            }
            Rule::single_expr => {
                // a single expression is made of a 'subject' and then an accessor like a
                // an index, property_access or func args. So, we firstly convert the
                // subject into an ast_node and then deal with a potential 'accessor'...
                let subject_expr = expr.next().unwrap().into_inner().next().unwrap();
                let subject_rule = subject_expr.as_rule();

                let subject = match subject_rule {
                    // We throw away the '#' here since we already know that it is an intrinsic call
                    Rule::intrinsic_expr => Ok(ab.node(Expression::Intrinsic(IntrinsicKey {
                        name: self.allocator.alloc_str(subject_expr.as_str()),
                    }))),
                    Rule::import_expr => {
                        // we only care about the string literal here
                        let import_call = subject_expr.into_inner().next().unwrap();
                        let import_path = import_call.into_inner().next().unwrap();
                        let s = import_path.as_span().as_str();
                        let module_idx = self.resolver.add_module(s, Some(ab.pos))?;

                        // get the string, but then convert into an AstNode using the string literal ast info
                        Ok(ab.node(Expression::Import(
                            self.builder_from_pair(&import_path).node(Import {
                                path: self.allocator.alloc_str(s),
                                index: module_idx,
                            }),
                        )))
                    }
                    Rule::literal_expr => Ok(ab.node(Expression::LiteralExpr(
                        self.transform_literal(subject_expr)?,
                    ))),
                    Rule::variable_expr => {
                        // so since this is going to be an access_name, which is a list of 'ident' rules,
                        // we can directly convert this into a VariableExpr
                        let mut var_expr = subject_expr.into_inner();
                        let access_name_inner = var_expr.next().unwrap();
                        let access_name = self.transform_access_name(access_name_inner)?;
                        let type_args = var_expr.next().map_or(Ok(ab.empty_slice()), |ty| {
                            ab.try_collect(ty.into_inner().map(|x| self.transform_type(x)))
                        })?;

                        Ok(ab.node(Expression::Variable(VariableExpr {
                            name: access_name,
                            type_args,
                        })))
                    }
                    Rule::paren_expr => self.transform_expression(subject_expr),
                    k => panic!("unexpected rule within expr: {:?}", k),
                };

                // now let's check if there is an 'accessor' node with the subject. Since there
                // can be zero or more accessors, we need continue looking at each rule until there
                // are no more accessors. If there is an accessor, we pattern match for the type,
                // transform the old 'subject' and continue
                let expr_node = expr.fold(subject, |prev_subject, accessor| {
                    let prev_subject = prev_subject?;
                    match accessor.as_rule() {
                        Rule::property_access => {
                            Ok(ab.node(Expression::PropertyAccess(PropertyAccessExpr {
                                subject: prev_subject,

                                // it's safe to unwrap here since property access will always
                                // provide the ident rule as the first one, otherwise it is a parsing error
                                property: self
                                    .transform_name(accessor.into_inner().next().unwrap())?,
                            })))
                        }
                        Rule::fn_args => {
                            // if it is func args, we need convert the 'subject' which is going
                            // to be a VariableExpr into a FunctionCallExpr
                            Ok(ab.node(Expression::FunctionCall(FunctionCallExpr {
                                subject: prev_subject,
                                args: self.builder_from_pair(&accessor).node(FunctionCallArgs {
                                    entries: ab.try_collect(
                                        accessor
                                            .into_inner()
                                            .map(|x| self.transform_expression(x)),
                                    )?,
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
                                self.transform_expression(accessor.into_inner().next().unwrap())?;

                            // @@Cutnpaste: move this into a seprate function for transpilling built-in functions
                            Ok(ab.node(Expression::FunctionCall(FunctionCallExpr {
                                subject: ab.node(Expression::Variable(VariableExpr {
                                    name: ab.make_single_access_name("index"),
                                    type_args: ab.empty_slice(),
                                })),
                                args: ab.node(FunctionCallArgs {
                                    entries: self.allocator.alloc([prev_subject, index_expr]),
                                }),
                            })))
                        }
                        k => panic!("unexpected rule within variable expr: {:?}", k),
                    }
                });

                // since there can be zero or more 'accessor' rules, we are sure that the current
                // expr has been transformed as required, essentially nesting each form of
                // accessor in each other
                expr_node
            }
            k => panic!("unexpected rule within expr: {:?}", k),
        }
    }

    pub(crate) fn transform_block(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, Block<'ast>>> {
        let ab = self.builder_from_pair(&pair);

        match pair.as_rule() {
            Rule::block => {
                let block = pair.into_inner().next().unwrap();

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
                        let append_else = Cell::new(true);
                        let cases = ab.try_collect(
                            block
                                .into_inner()
                                .map(|if_condition| {
                                    let block_builder = self.builder_from_pair(&if_condition);

                                    match if_condition.as_rule() {
                                        Rule::if_block => {
                                            let mut components = if_condition.into_inner();

                                            // get the clause and block from the if-block components
                                            let clause = self.transform_expression(
                                                components.next().unwrap(),
                                            )?;
                                            let block =
                                                self.transform_block(components.next().unwrap())?;

                                            Ok(block_builder.node(MatchCase {
                                                pattern: block_builder.node(Pattern::If(
                                                    IfPattern {
                                                        pattern: block_builder
                                                            .node(Pattern::Ignore),
                                                        condition: clause,
                                                    },
                                                )),
                                                expr: self
                                                    .builder_from_node(&block)
                                                    .node(Expression::Block(block)),
                                            }))
                                        }
                                        Rule::else_block => {
                                            append_else.set(false);

                                            let block = self.transform_block(
                                                if_condition.into_inner().next().unwrap(),
                                            )?;

                                            Ok(block_builder.node(MatchCase {
                                                pattern: block_builder.node(Pattern::Ignore),
                                                expr: self
                                                    .builder_from_node(&block)
                                                    .node(Expression::Block(block)),
                                            }))
                                        }
                                        k => {
                                            panic!("unexpected rule within if-else-block: {:?}", k)
                                        }
                                    }
                                })
                                .chain(
                                    {
                                        if append_else.get() {
                                            Some(Ok(ab.node(MatchCase {
                                                pattern: ab.node(Pattern::Ignore),
                                                expr: ab.node(Expression::Block(ab.node(
                                                    Block::Body(BodyBlock {
                                                        statements: ab.empty_slice(),
                                                        expr: None,
                                                    }),
                                                ))),
                                            })))
                                        } else {
                                            None
                                        }
                                    }
                                    .into_iter(),
                                ),
                        )?;

                        // if no else-block was provided, we need to add one manually

                        Ok(ab.node(Block::Match(MatchBlock {
                            subject: ab.make_variable(ab.make_boolean(true)),
                            cases,
                        })))
                    }
                    Rule::match_block => {
                        let mut match_block = block.into_inner();

                        // firstly get the expresion condition from the match block, the
                        // next rule will be a bunch of match_case rules which can be
                        // converted into ast using the pattern and block implementations...
                        let subject = self.transform_expression(match_block.next().unwrap())?;
                        let match_cases = match_block.next().unwrap();

                        let cases = ab.try_collect(match_cases.into_inner().map(|case| {
                            let case_builder = self.builder_from_pair(&case);

                            match case.as_rule() {
                                Rule::match_case => {
                                    let mut components = case.into_inner();

                                    let pattern =
                                        self.transform_pattern(components.next().unwrap())?;
                                    let expr =
                                        self.transform_expression(components.next().unwrap())?;

                                    Ok(case_builder.node(MatchCase { pattern, expr }))
                                }
                                k => panic!("unexpected rule within match_case: {:?}", k),
                            }
                        }))?;

                        Ok(ab.node(Block::Match(MatchBlock { subject, cases })))
                    }
                    Rule::loop_block => {
                        let body_block =
                            self.transform_block(block.into_inner().next().unwrap())?;
                        Ok(ab.node(Block::Loop(body_block)))
                    }
                    Rule::for_block => {
                        let mut for_block = block.into_inner();

                        let pattern = self.transform_pattern(for_block.next().unwrap())?;
                        let pat_builder = self.builder_from_node(&pattern);

                        let iterator = self.transform_expression(for_block.next().unwrap())?;
                        let iter_builder = self.builder_from_node(&iterator);

                        let body = self.transform_block(for_block.next().unwrap())?;
                        let body_builder = self.builder_from_node(&body);

                        Ok(ab.node(Block::Loop(ab.node(Block::Match(MatchBlock {
                            subject: iter_builder.node(Expression::FunctionCall(
                                FunctionCallExpr {
                                    subject: iter_builder.node(Expression::Variable(
                                        VariableExpr {
                                            name: ab.make_single_access_name("next"),
                                            type_args: self.allocator.alloc([]),
                                        },
                                    )),
                                    args: iter_builder.node(FunctionCallArgs {
                                        entries: self.allocator.alloc([iterator]),
                                    }),
                                },
                            )),
                            cases: self.allocator.alloc([
                                body_builder.node(MatchCase {
                                    pattern: pat_builder.node(Pattern::Enum(EnumPattern {
                                        name: iter_builder.make_single_access_name("Some"),
                                        args: self.allocator.alloc([pattern]),
                                    })),
                                    expr: body_builder.node(Expression::Block(body)),
                                }),
                                body_builder.node(MatchCase {
                                    pattern: pat_builder.node(Pattern::Enum(EnumPattern {
                                        name: iter_builder.make_single_access_name("None"),
                                        args: self.allocator.alloc([]),
                                    })),
                                    expr: body_builder.node(Expression::Block(body_builder.node(
                                        Block::Body(
                                            BodyBlock {
                                                statements:
                                                    self.allocator.alloc([
                                                        body_builder.node(Statement::Break),
                                                    ]),
                                                expr: None,
                                            },
                                        ),
                                    ))),
                                }),
                            ]),
                        })))))
                    }
                    Rule::while_block => {
                        let mut while_block = block.into_inner();

                        let condition = self.transform_expression(while_block.next().unwrap())?;
                        let condition_builder = self.builder_from_node(&condition);

                        let body = self.transform_block(while_block.next().unwrap())?;
                        let body_builder = self.builder_from_node(&body);

                        Ok(ab.node(Block::Loop(ab.node(Block::Match(MatchBlock {
                            subject: condition,
                            cases: self.allocator.alloc([
                                body_builder.node(MatchCase {
                                    pattern: condition_builder.node(Pattern::Enum(EnumPattern {
                                        name: condition_builder.make_boolean(true),
                                        args: ab.empty_slice(),
                                    })),
                                    expr: body_builder.node(Expression::Block(body)),
                                }),
                                body_builder.node(MatchCase {
                                    pattern: condition_builder.node(Pattern::Enum(EnumPattern {
                                        name: condition_builder.make_boolean(false),
                                        args: ab.empty_slice(),
                                    })),
                                    expr: body_builder.node(Expression::Block(body_builder.node(
                                        Block::Body(
                                            BodyBlock {
                                                statements:
                                                    self.allocator.alloc([
                                                        body_builder.node(Statement::Break),
                                                    ]),
                                                expr: None,
                                            },
                                        ),
                                    ))),
                                }),
                            ]),
                        })))))
                    }
                    Rule::body_block => self.transform_block(block),
                    k => panic!("unexpected rule within block variant: {:?}", k),
                }
            }
            Rule::body_block => {
                let mut statements = pair.into_inner();
                let last_statement = statements.next_back();

                let (statements, expr) = match last_statement {
                    Some(last) => {
                        let parsed = self.transform_statement(last)?;
                        let ab = self.builder_from_node(&parsed);
                        match parsed.body {
                            Statement::Expr(expr) => (
                                ab.try_collect(statements.map(|s| self.transform_statement(s)))?,
                                Some(ab.existing_node(expr.body)),
                            ),
                            _ => (
                                ab.try_collect(
                                    statements
                                        .map(|s| self.transform_statement(s))
                                        .chain(once(Ok(parsed))),
                                )?,
                                None,
                            ),
                        }
                    }
                    None => (ab.empty_slice(), None),
                };

                Ok(ab.node(Block::Body(BodyBlock { statements, expr })))
            }
            k => panic!("unexpected rule within block: {:?}", k),
        }
    }

    pub(crate) fn transform_statement(
        &mut self,
        pair: HashPair<'_>,
    ) -> ParseResult<AstNode<'ast, Statement<'ast>>> {
        let ab = self.builder_from_pair(&pair);

        match pair.as_rule() {
            Rule::statement => {
                let statement = pair.into_inner().next().unwrap();

                // since we have block statements and semi statements, we can check here
                // to see which path it is, if this is a block statement, we just call
                // into_ast(resolver) since there is an implementation for block convetsions
                match statement.as_rule() {
                    Rule::block => Ok(ab.node(Statement::Block(self.transform_block(statement)?))),
                    Rule::break_st => Ok(ab.node(Statement::Break)),
                    Rule::continue_st => Ok(ab.node(Statement::Continue)),
                    Rule::return_st => {
                        let ret_expr = statement.into_inner().next();

                        if let Some(node) = ret_expr {
                            Ok(ab.node(Statement::Return(Some(self.transform_expression(node)?))))
                        } else {
                            Ok(ab.node(Statement::Return(None)))
                        }
                    }
                    Rule::let_st => {
                        // the first rule will be the pattern which can be automatically converted, whereas
                        // then we have a trait bound and finally an optional expression which is used as an
                        // assignment to the let statement
                        let mut components = statement.into_inner();

                        let pattern = self.transform_pattern(components.next().unwrap())?;

                        let bound_or_ty = components.next();
                        let (bound, ty, value) = match bound_or_ty {
                            Some(pair) => match pair.as_rule() {
                                Rule::bound => {
                                    let bound = Some(self.transform_bound(pair)?);

                                    let ty_or_expr = components.next();

                                    match ty_or_expr {
                                        Some(r) => match r.as_rule() {
                                            Rule::any_type => (
                                                bound,
                                                Some(self.transform_type(r)?),
                                                // check if the optional value component is present with the let statement...
                                                components
                                                    .next()
                                                    .map(|p| self.transform_expression(p))
                                                    .transpose()?,
                                            ),
                                            Rule::expr => {
                                                (bound, None, Some(self.transform_expression(r)?))
                                            }
                                            k => {
                                                panic!(
                                                    "Unexpected rule within ty_or_expr: {:?}",
                                                    k
                                                )
                                            }
                                        },
                                        None => (bound, None, None),
                                    }
                                }
                                Rule::any_type => (
                                    None,
                                    Some(self.transform_type(pair)?),
                                    components
                                        .next()
                                        .map(|p| self.transform_expression(p))
                                        .transpose()?,
                                ),
                                Rule::expr => (None, None, Some(self.transform_expression(pair)?)),
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
                            self.transform_expression(components.next().unwrap())?;

                        // if no rhs is present, this is just an singular expression instead of an
                        // assignment
                        match components.next() {
                            Some(op_wrap) => {
                                // get the assignment operator out of 'assign_op'
                                let op = op_wrap.into_inner().next().unwrap();
                                let transform = convert_rule_into_fn_call(&op.as_rule());

                                let mut rhs =
                                    self.transform_expression(components.next().unwrap())?;

                                // transform lhs if we're using a non-eq assignment operator into the appropriate
                                // function call...
                                match transform {
                                    Some(fn_name) => {
                                        // Representing '$internal' as an identifier
                                        let builder = self.builder_from_node(&rhs);
                                        let internal_node = ab.make_internal_node();

                                        let internal_decl = self.builder_from_node(&lhs).node(
                                            Statement::Assign(AssignStatement {
                                                lhs: ab.make_internal_node(),
                                                rhs: lhs,
                                            }),
                                        );

                                        // transform the right hand side into the appropriate expression, by representing the
                                        // modification operator into a function call and then setting the lhs and rhs as
                                        // arguments to the function call. So, essentially the expression `lhs += rhs` is transformed
                                        // into `lhs = lhs + rhs`
                                        rhs = builder.node(Expression::FunctionCall(
                                            FunctionCallExpr {
                                                subject: builder.node(Expression::Variable(
                                                    VariableExpr {
                                                        name: builder
                                                            .make_single_access_name(fn_name),
                                                        type_args: self.allocator.alloc([]),
                                                    },
                                                )),
                                                args: self.builder_from_node(&rhs).node(
                                                    FunctionCallArgs {
                                                        entries: self
                                                            .allocator
                                                            .alloc([ab.make_internal_node(), rhs]),
                                                    },
                                                ),
                                            },
                                        ));

                                        // make the assignment
                                        let assignment =
                                            ab.node(Statement::Assign(AssignStatement {
                                                lhs: ab.make_internal_node(),
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
                                        Ok(ab.node(Statement::Expr(builder.node(
                                            Expression::Block(
                                                builder.node(
                                                    Block::Body(
                                                        BodyBlock {
                                                            statements: self.allocator.alloc([
                                                                internal_decl,
                                                                assignment,
                                                            ]),
                                                            expr: Some(internal_node), // the return statement is just the internal node
                                                        },
                                                    ),
                                                ),
                                            ),
                                        ))))
                                    }
                                    None => {
                                        Ok(ab
                                            .node(Statement::Assign(AssignStatement { lhs, rhs })))
                                    }
                                }
                            }
                            None => Ok(ab.node(Statement::Expr(lhs))),
                        }
                    }
                    Rule::struct_def => {
                        let mut components = statement.into_inner();
                        let name = self.transform_name(components.next().unwrap())?;

                        let bound_or_fields = components.next().unwrap();
                        let (bound, entries) = match bound_or_fields.as_rule() {
                            Rule::bound => (
                                Some(self.transform_bound(bound_or_fields)?),
                                // It's guaranteed to have zero or more struct def fields and so it is
                                // safe to unwrap the following rule after the bound...
                                ab.try_collect(
                                    components
                                        .next()
                                        .unwrap()
                                        .into_inner()
                                        .map(|x| self.transform_struct_def_entry(x)),
                                )?,
                            ),

                            Rule::struct_def_fields => (
                                None,
                                ab.try_collect(
                                    bound_or_fields
                                        .into_inner()
                                        .map(|x| self.transform_struct_def_entry(x)),
                                )?,
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
                        let name = self.transform_name(components.next().unwrap())?;

                        let bound_or_fields = components.next().unwrap();
                        let (bound, entries) = match bound_or_fields.as_rule() {
                            Rule::bound => (
                                Some(self.transform_bound(bound_or_fields)?),
                                ab.try_collect(
                                    components
                                        .next()
                                        .unwrap()
                                        .into_inner()
                                        .map(|x| self.transform_enum_def_entry(x)),
                                )?,
                            ),
                            // It's guaranteed to have zero or more enum def fields and so it is
                            // safe to unwrap the following rule after the bound...
                            Rule::enum_fields => (
                                None,
                                ab.try_collect(
                                    bound_or_fields
                                        .into_inner()
                                        .map(|x| self.transform_enum_def_entry(x)),
                                )?,
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
                        let name = self.transform_name(components.next().unwrap())?;
                        let bound = self.transform_bound(components.next().unwrap())?;

                        let fn_rule = components.next().unwrap();
                        debug_assert_eq!(fn_rule.as_rule(), Rule::fn_type);

                        let trait_type = self.transform_type(fn_rule)?;

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
            Rule::expr => Ok(ab.node(Statement::Expr(self.transform_expression(pair)?))),
            k => panic!("unexpected rule within statement: {:?}", k),
        }
    }
}

#[cfg(test)]
mod tests {
    // use pest::Parser;

    // use super::*;

    // pub(crate) fn parse_input<T>(rule: Rule, input: &str) -> AstNode<T>
    // where
    //     for<'a> HashPair<'a>: IntoAstNode<T>,
    // {
    //     let resolver = SeqModuleResolver::new();
    //     let mut result = grammar::HashGrammar::parse(rule, input).unwrap();
    //     let parsed: AstNode<T> = result.next().unwrap().into_ast(&resolver);
    //     parsed
    // }

    // #[test]
    // pub(crate) fn test_name() {
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
    // pub(crate) fn test_access_name() {
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
