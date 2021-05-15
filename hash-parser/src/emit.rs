use std::{iter, vec};

use num::BigInt;

use crate::{ast::*, grammar::Rule, location::Location, modules::ModuleIdx, precedence::climb};

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

pub struct AstBuilder {
    pos: Location,
    module: ModuleIdx,
}

impl AstBuilder {
    pub fn from_pair(pair: &pest::iterators::Pair<'_, Rule>) -> AstBuilder {
        let span = pair.as_span();
        let pos = Location::Span(span.start(), span.end());
        AstBuilder {
            pos,
            module: 0, // @TODO: add multiple module support
        }
    }

    pub fn from_node<T>(node: &AstNode<T>) -> AstBuilder {
        AstBuilder {
            pos: node.pos,
            module: node.module,
        }
    }

    pub fn node<T>(&self, inner: T) -> AstNode<T> {
        AstNode {
            body: Box::new(inner),
            pos: self.pos,
            module: self.module,
        }
    }

    pub fn node_from_pair<T>(
        &self,
        inner: T,
        pair: &pest::iterators::Pair<'_, Rule>,
    ) -> AstNode<T> {
        let span = pair.as_span();
        let pos = Location::Span(span.start(), span.end());

        AstNode {
            body: Box::new(inner),
            pos,
            module: self.module,
        }
    }
}

type HashPair<'a> = pest::iterators::Pair<'a, Rule>;

impl IntoAstNode<Name> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Name> {
        match self.as_rule() {
            Rule::ident => AstBuilder::from_pair(&self).node(Name {
                string: self.as_str().to_owned(),
            }),
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<StructDefEntry> for HashPair<'_> {
    fn into_ast(self) -> AstNode<StructDefEntry> {
        match self.as_rule() {
            Rule::struct_def_field => {
                let ab = AstBuilder::from_pair(&self);
                let mut components = self.into_inner();

                let name = components.next().unwrap().into_ast();
                let next_node = components.next();

                let (ty, default) = match next_node {
                    Some(pair) => match pair.as_rule() {
                        Rule::any_type => (
                            Some(pair.into_ast()),
                            components.next().map(|p| p.into_ast()),
                        ),
                        Rule::expr => (None, Some(pair.into_ast())),
                        k => panic!("unexpected rule within literal_pattern: {:?}", k),
                    },
                    None => (None, None),
                };

                ab.node(StructDefEntry { name, ty, default })
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<EnumDefEntry> for HashPair<'_> {
    fn into_ast(self) -> AstNode<EnumDefEntry> {
        match self.as_rule() {
            Rule::enum_field => {
                let ab = AstBuilder::from_pair(&self);
                let mut components = self.into_inner();

                let name = components.next().unwrap().into_ast();
                let args = components.map(|p| p.into_ast()).collect();

                ab.node(EnumDefEntry { name, args })
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<Bound> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Bound> {
        match self.as_rule() {
            Rule::bound => {
                let ab = AstBuilder::from_pair(&self);
                let mut components = self.into_inner();

                // firsly convert the type args by just iterating the inner component
                // of the type_args rule...
                let type_args: Vec<AstNode<Type>> = components
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|p| p.into_ast())
                    .collect();

                // check if there are any trait_bounds attached with this bound
                let trait_bounds = match components.next() {
                    Some(pair) => pair.into_inner().map(|p| p.into_ast()).collect(),
                    None => vec![],
                };

                ab.node(Bound {
                    type_args,
                    trait_bounds,
                })
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<TraitBound> for HashPair<'_> {
    fn into_ast(self) -> AstNode<TraitBound> {
        match self.as_rule() {
            Rule::trait_bound => {
                let ab = AstBuilder::from_pair(&self);
                let mut components = self.into_inner();

                // convert the access_name rule into a AstNode, each trait bound is guaranteed
                // to have an access name, so it's safe to unwrap here...
                let name = components.next().unwrap().into_ast();

                // convert any type args the trait bound contains
                let type_args = match components.next() {
                    Some(pair) => pair.into_inner().map(|p| p.into_ast()).collect(),
                    None => vec![],
                };

                ab.node(TraitBound { name, type_args })
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<AccessName> for HashPair<'_> {
    fn into_ast(self) -> AstNode<AccessName> {
        match self.as_rule() {
            Rule::access_name => AstBuilder::from_pair(&self).node(AccessName {
                names: self.into_inner().map(|p| p.into_ast()).collect(),
            }),
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
    fn into_ast(self) -> AstNode<Type> {
        match self.as_rule() {
            Rule::any_type => {
                let ab = AstBuilder::from_pair(&self);
                let in_type = self.into_inner().next().unwrap();
                match in_type.as_rule() {
                    Rule::infer_type => ab.node(Type::Infer),
                    Rule::named_type => {
                        let mut in_named = in_type.into_inner();

                        let name = in_named.next().unwrap().into_ast();
                        let type_args = in_named
                            .next()
                            .map(|n| n.into_inner().map(|p| p.into_ast()).collect())
                            .unwrap_or_default();

                        ab.node(Type::Named(NamedType { name, type_args }))
                    }
                    Rule::fn_type => {
                        let mut in_func = in_type.into_inner();

                        let args = in_func.next().unwrap().into_inner().map(|p| p.into_ast());
                        let ret = in_func.next().unwrap().into_ast();

                        let args_ret = args.chain(iter::once(ret));
                        ab.node(Type::Named(NamedType {
                            name: single_access_name(&ab, FUNCTION_TYPE_NAME),
                            type_args: args_ret.collect(),
                        }))
                    }
                    Rule::tuple_type => {
                        let inner = in_type.into_inner().map(|p| p.into_ast());

                        ab.node(Type::Named(NamedType {
                            name: single_access_name(&ab, TUPLE_TYPE_NAME),
                            type_args: inner.collect(),
                        }))
                    }
                    Rule::list_type => {
                        let inner = in_type.into_inner().map(|p| p.into_ast());

                        // list type should only have one type
                        debug_assert_eq!(inner.size_hint().0, 1);

                        ab.node(Type::Named(NamedType {
                            name: single_access_name(&ab, LIST_TYPE_NAME),
                            type_args: inner.collect(),
                        }))
                    }
                    Rule::set_type => {
                        let inner = in_type.into_inner().map(|p| p.into_ast());

                        // set type should only have one type
                        debug_assert_eq!(inner.size_hint().0, 1);

                        ab.node(Type::Named(NamedType {
                            name: single_access_name(&ab, SET_TYPE_NAME),
                            type_args: inner.collect(),
                        }))
                    }
                    Rule::map_type => {
                        let inner = in_type.into_inner().map(|p| p.into_ast());

                        // map type should only have a type for a key and a value
                        debug_assert_eq!(inner.size_hint().0, 2);

                        ab.node(Type::Named(NamedType {
                            name: single_access_name(&ab, MAP_TYPE_NAME),
                            type_args: inner.collect(),
                        }))
                    }
                    Rule::existential_type => ab.node(Type::Existential),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<Literal> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Literal> {
        let ab = AstBuilder::from_pair(&self);

        match self.as_rule() {
            // If the literal is wrapped in a literal_expr, we unwrap it and then just convert
            // the internal contents of it using the same implementation...
            Rule::literal_expr => self.into_inner().next().unwrap().into_ast(),
            Rule::integer_literal => {
                let inner = self.into_inner().next().unwrap();
                // this could be binary, hex, octal or decimal...
                match inner.as_rule() {
                    Rule::decimal_literal => {
                        // check if there is a float exp component since we allow this, although if the specified exponent is
                        // float, we'll cast the result to decimal...
                        let mut components = inner.into_inner();
                        let num = components.next().unwrap();

                        let val = BigInt::parse_bytes(num.as_str().as_bytes(), 10).unwrap();

                        ab.node(Literal::Int(val))
                    }
                    Rule::hex_literal => {
                        let val = BigInt::parse_bytes(inner.as_str().as_bytes(), 16).unwrap();
                        ab.node(Literal::Int(val))
                    }
                    Rule::octal_literal => {
                        let val = BigInt::parse_bytes(inner.as_str().as_bytes(), 8).unwrap();
                        ab.node(Literal::Int(val))
                    }
                    Rule::bin_literal => {
                        let val = BigInt::parse_bytes(inner.as_str().as_bytes(), 2).unwrap();
                        ab.node(Literal::Int(val))
                    }
                    _ => unreachable!(),
                }
            }
            Rule::float_literal => {
                let mut components = self.into_inner();

                // float_literal is made of three parts, the integer part, fractical part
                // and an optional exponent part...
                let float = components.next().unwrap();

                let mut value: f64 = float
                    .as_str()
                    .parse()
                    .unwrap_or_else(|_| panic!("Invalid float")); // @@Incomplete: change this to report an ast error!

                // apply exponent if any
                value = match components.next() {
                    Some(pair) => {
                        // since it might also have a -/+ sign, we need join it with the exponent int literal...
                        // @@Speed: is this a good way of joining strings...?
                        let str_val = pair
                            .into_inner()
                            .map(|p| p.as_str())
                            .collect::<Vec<&str>>()
                            .join("");

                        let exponent: i32 = str_val
                            .parse()
                            .unwrap_or_else(|_| panic!("Invalid float exp: {}", str_val)); // @@Incomplete: change this to report an ast error!

                        value.powi(exponent)
                    }
                    None => value,
                };

                ab.node(Literal::Float(value))
            }
            Rule::char_literal => {
                let c: char = self.as_span().as_str().chars().next().unwrap();
                ab.node(Literal::Char(c))
            }
            Rule::string_literal => {
                let s = String::from(self.as_span().as_str());
                ab.node(Literal::Str(s))
            }
            Rule::list_literal => {
                // since list literals are just a bunch of expressions, we just call
                // into_ast() on each member and collect at the end
                let elements = self.into_inner().map(|p| p.into_ast()).collect();

                ab.node(Literal::List(ListLiteral { elements }))
            }
            Rule::set_literal => {
                // since set literals are just a bunch of expressions, we just call
                // into_ast() on each member and collect at the end
                let elements = self.into_inner().map(|p| p.into_ast()).collect();

                ab.node(Literal::Set(SetLiteral { elements }))
            }
            Rule::tuple_literal => {
                // since tuple literals are just a bunch of expressions, we just call
                // into_ast() on each member and collect at the end
                let elements = self.into_inner().map(|p| p.into_ast()).collect();

                ab.node(Literal::Tuple(TupleLiteral { elements }))
            }
            Rule::map_literal => {
                // A map is made of a vector of 'map_entries' rules, which are just two
                // expressions.
                let elements = self
                    .into_inner()
                    .map(|p| {
                        let mut items = p.into_inner().map(|pi| pi.into_ast());

                        (items.next().unwrap(), items.next().unwrap())
                    })
                    .collect();

                ab.node(Literal::Map(MapLiteral { elements }))
            }
            Rule::fn_literal => {
                // we're looking for a number of function arguments, an optional return and
                // a function body which is just an expression.
                let mut components = self.into_inner();

                // firstly, take care of the function parameters...
                let args = components
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|param| {
                        let mut param_components = param.into_inner();

                        // get the name of identifier
                        let name = param_components.next().unwrap().into_ast();

                        // if no type is specified for the param, we just set it to none
                        let ty = param_components.next().map(|t| t.into_ast());

                        ab.node(FunctionDefArg { name, ty })
                    })
                    .collect();

                // now check here if the next rule is either a type or a expression,
                // if it is a type, we expect that there are two more rules to follow
                // since function literals cannot be without a fn_body
                let fn_type_or_body = components.next().unwrap();

                let (return_ty, fn_body) = match fn_type_or_body.as_rule() {
                    Rule::any_type => {
                        let body = components.next().unwrap();
                        (Some(fn_type_or_body.into_ast()), body.into_ast())
                    }
                    Rule::expr => (None, fn_type_or_body.into_ast()),
                    _ => unreachable!(),
                };
                ab.node(Literal::Function(FunctionDef {
                    args,
                    return_ty,
                    fn_body,
                }))
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<LiteralPattern> for HashPair<'_> {
    fn into_ast(self) -> AstNode<LiteralPattern> {
        match self.as_rule() {
            Rule::literal_pattern => {
                let pat = self.into_inner().next().unwrap();

                // we prematurely convert the first node into a Literal, and then
                // pattern match on the literal, converting into a Literal pattern
                let node: AstNode<Literal> = pat.into_ast();
                let builder = AstBuilder::from_node(&node);

                // essentially cast the literal into a literal_pattern
                match *node.body {
                    Literal::Str(s) => builder.node(LiteralPattern::Str(s)),
                    Literal::Char(s) => builder.node(LiteralPattern::Char(s)),
                    Literal::Float(s) => builder.node(LiteralPattern::Float(s)),
                    Literal::Int(s) => builder.node(LiteralPattern::Int(s)),
                    k => panic!(
                        "literal_pattern should be string, float, char or int, got : {:?}",
                        k
                    ),
                }
            }
            k => panic!("unexpected rule within literal_pattern: {:?}", k),
        }
    }
}

impl IntoAstNode<Pattern> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Pattern> {
        let ab = AstBuilder::from_pair(&self);

        match self.as_rule() {
            Rule::pattern => self.into_inner().next().unwrap().into_ast(),
            Rule::single_pattern => {
                let pat = self.into_inner().next().unwrap();

                match pat.as_rule() {
                    Rule::enum_pattern => {
                        let mut components = pat.into_inner();

                        let name = components.next().unwrap().into_ast();
                        let args = components
                            .next()
                            .unwrap()
                            .into_inner()
                            .map(|p| p.into_ast())
                            .collect();

                        ab.node(Pattern::Enum(EnumPattern { name, args }))
                    }
                    Rule::struct_pattern => {
                        let mut components = pat.into_inner();

                        let name = components.next().unwrap().into_ast();

                        // If there is no binding part of the destructuring pattern, as in if
                        // no pattern on the right-handside, we use the name of the field as a
                        // binding pattern here...
                        let entries = components
                            .next()
                            .unwrap()
                            .into_inner()
                            .map(|p| {
                                let mut field = p.into_inner();

                                let name: AstNode<Name> = field.next().unwrap().into_ast();

                                let pattern = match field.next() {
                                    Some(pat) => pat.into_ast(),
                                    None => AstBuilder::from_node(&name)
                                        .node(Pattern::Binding(name.clone())),
                                };

                                AstBuilder::from_node(&name)
                                    .node(DestructuringPattern { name, pattern })
                            })
                            .collect();

                        ab.node(Pattern::Struct(StructPattern { name, entries }))
                    }
                    Rule::namespace_pattern => {
                        let patterns = pat
                            .into_inner()
                            .map(|p| {
                                let mut field = p.into_inner();

                                let name: AstNode<Name> = field.next().unwrap().into_ast();

                                let pattern = match field.next() {
                                    Some(pat) => pat.into_ast(),
                                    None => AstBuilder::from_node(&name)
                                        .node(Pattern::Binding(name.clone())),
                                };

                                AstBuilder::from_node(&name)
                                    .node(DestructuringPattern { name, pattern })
                            })
                            .collect();

                        ab.node(Pattern::Namespace(NamespacePattern { patterns }))
                    }
                    Rule::binding_pattern => {
                        let name = pat.into_inner().next().unwrap().into_ast();
                        ab.node(Pattern::Binding(name))
                    }
                    Rule::ignore_pattern => ab.node(Pattern::Ignore),
                    // @@Cleanup: is this right, can we avoid this by just using another AstNode here?
                    Rule::literal_pattern => ab.node(Pattern::Literal(*pat.into_ast().body)),
                    Rule::tuple_pattern => ab.node(Pattern::Tuple(TuplePattern {
                        elements: pat.into_inner().map(|p| p.into_ast()).collect(),
                    })),

                    // grouped pattern is just a pattern surrounded by parenthesees, to specify precidence...
                    Rule::grouped_pattern => pat.into_ast(),
                    k => panic!("unexpected rule within single_pattern: {:?}", k),
                }
            }
            Rule::compound_pattern => {
                let mut components = self.into_inner();

                let pattern_rule = components.next().unwrap();
                let mut pats = pattern_rule.into_inner().map(|p| p.into_ast());

                // there are can only be a lhs and rhs
                debug_assert_eq!(pats.size_hint().0, 2);

                let lhs = ab.node(Pattern::Or(OrPattern {
                    a: pats.next().unwrap(),
                    b: pats.next().unwrap(),
                }));

                match components.next() {
                    Some(k) => {
                        // the 'if' guared expects the rhs to be an expression
                        debug_assert_eq!(k.as_rule(), Rule::expr);

                        AstBuilder::from_pair(&k).node(Pattern::If(IfPattern {
                            pattern: lhs,
                            condition: k.into_ast(),
                        }))
                    }
                    None => lhs,
                }
            }
            k => panic!("unexpected rule within expr: {:?}", k),
        }
    }
}

impl IntoAstNode<Expression> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Expression> {
        let ab = AstBuilder::from_pair(&self);

        match self.as_rule() {
            Rule::expr => {
                let expr = self.into_inner().next().unwrap();

                match expr.as_rule() {
                    Rule::block => ab.node(Expression::Block(expr.into_ast())),
                    Rule::struct_literal => ab.node(Expression::LiteralExpr(expr.into_ast())),
                    Rule::binary_expr => {
                        let mut items = expr.clone().into_inner();

                        // if this is an actual binary expr, we need to check if the second token is a
                        // binary_op and the invoke prec_climber.
                        let lhs = items.next().unwrap();

                        match items.next() {
                            Some(_) => climb(expr),
                            None => lhs.into_ast(),
                        }
                    }
                    k => panic!("unexpected rule within inner_expr: {:?}", k),
                }
            }
            Rule::typed_expr => {
                let expr = self.into_inner().next().unwrap();
                let mut items = expr.into_inner();

                // the next is a unary expression...
                let inner = items.next().unwrap();

                // check if this expression has a type...
                match items.next() {
                    Some(ty) => ab.node(Expression::Typed(TypedExpr {
                        ty: ty.into_ast(), // convert the type into an AstNode
                        expr: inner.into_ast(),
                    })),
                    None => inner.into_ast(),
                }
            }
            Rule::unary_expr => {
                let mut expr = self.into_inner();
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

                        ab.node(Expression::FunctionCall(FunctionCallExpr {
                            subject: ab.node(Expression::Variable(VariableExpr {
                                name: ab.node(AccessName {
                                    names: vec![ab.node(Name { string: fn_call })],
                                }),
                                type_args: vec![],
                            })),
                            args: ab.node(FunctionCallArgs {
                                entries: vec![operand.into_ast()],
                            }),
                        }))
                    }
                    _ => op_or_single_expr.into_ast(),
                }
            }
            Rule::single_expr => {
                let mut expr = self.into_inner();

                // a single expression is made of a 'subject' and then an accessor like a
                // an index, property_access or func args. So, we firstly convert the
                // subject into an ast_node and then deal with a potential 'accessor'...
                let subject_expr = expr.next().unwrap().into_inner().next().unwrap();
                let subject_rule = subject_expr.as_rule();

                let mut subject = match subject_rule {
                    Rule::intrinsic_expr => ab.node(Expression::Intrinsic(IntrinsicKey {
                        // @@Correctness: Currently, we preserve the '#' prefix for the intrinsic when
                        // working with the key, is this correct or should we throw away the '#'?
                        name: String::from(subject_expr.as_str()), // @@Redundant: Another uneccessary copy here??
                    })),
                    Rule::import_expr => {
                        // we only care about the string literal here
                        let import_call = subject_expr.into_inner().next().unwrap();
                        let import_path = import_call.into_inner().next().unwrap();
                        let s = String::from(import_path.as_span().as_str());

                        // get the string, but then convert into an AstNode using the string literal ast info
                        ab.node(Expression::Import(
                            AstBuilder::from_pair(&import_path).node(s),
                        ))
                    }
                    Rule::literal_expr => ab.node(Expression::LiteralExpr(subject_expr.into_ast())),
                    Rule::variable_expr => {
                        // so since this is going to be an access_name, which is a list of 'ident' rules,
                        // we can directly convert this into a VariableExpr
                        let mut var_expr = subject_expr.into_inner();

                        let access_name = var_expr.next().unwrap();

                        // is this even correct?
                        let names: Vec<AstNode<Name>> =
                            access_name.into_inner().map(|n| n.into_ast()).collect();

                        // check for type args...
                        if let Some(ty) = var_expr.next() {
                            ab.node(Expression::Variable(VariableExpr {
                                name: ab.node(AccessName { names }),
                                type_args: ty.into_inner().map(|p| p.into_ast()).collect(),
                            }))
                        } else {
                            ab.node(Expression::Variable(VariableExpr {
                                name: ab.node(AccessName { names }),
                                type_args: vec![],
                            }))
                        }
                    }
                    Rule::paren_expr => subject_expr.into_ast(),
                    k => panic!("unexpected rule within expr: {:?}", k),
                };

                // now let's check if there is an 'accessor' node with the subject. Since there
                // can be zero or more accessors, we need continue looking at each rule until there
                // are no more accessors. If there is an accessor, we pattern match for the type,
                // transform the old 'subject' and continue
                for accessor in expr {
                    subject = match accessor.as_rule() {
                        Rule::property_access => {
                            ab.node(Expression::PropertyAccess(PropertyAccessExpr {
                                subject,

                                // it's safe to unwrap here since property access will always
                                // provide the ident rule as the first one, otherwise it is a parsing error
                                property: accessor.into_inner().next().unwrap().into_ast(),
                            }))
                        }
                        Rule::fn_args => {
                            // if it is func args, we need convert the 'subject' which is going
                            // to be a VariableExpr into a FunctionCallExpr
                            ab.node(Expression::FunctionCall(FunctionCallExpr {
                                subject,
                                args: AstBuilder::from_pair(&accessor).node(FunctionCallArgs {
                                    entries: accessor.into_inner().map(|p| p.into_ast()).collect(),
                                }),
                            }))
                        }
                        // we need to convert this into a 'index' function call on the
                        // current variable
                        Rule::index_arg => {
                            // if subject isn't a variable, how tf did we end up here
                            debug_assert_eq!(subject_rule, Rule::variable_expr);

                            // this is the expression within the brackets.
                            let index_expr = accessor.into_inner().next().unwrap().into_ast();

                            // @@Cutnpase: move this into a seprate function for transpilling built-in functions
                            ab.node(Expression::FunctionCall(FunctionCallExpr {
                                subject: ab.node(Expression::Variable(VariableExpr {
                                    name: ab.node(AccessName {
                                        names: vec![ab.node(Name {
                                            string: String::from("index"),
                                        })],
                                    }),
                                    type_args: vec![],
                                })),
                                args: ab.node(FunctionCallArgs {
                                    entries: vec![subject, index_expr],
                                }),
                            }))
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
    fn into_ast(self) -> AstNode<Block> {
        let ab = AstBuilder::from_pair(&self);

        match self.as_rule() {
            Rule::block => {
                let block = self.into_inner().next().unwrap();

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
                        let mut cases: Vec<AstNode<MatchCase>> = vec![];
                        let mut append_else = true;

                        for if_condition in block.into_inner() {
                            let block_builder = AstBuilder::from_pair(&if_condition);

                            let pattern = match if_condition.as_rule() {
                                Rule::if_block => {
                                    let mut components = if_condition.into_inner();

                                    // get the clause and block from the if-block components
                                    let clause = components.next().unwrap().into_ast();
                                    let block = components.next().unwrap().into_ast();

                                    block_builder.node(MatchCase {
                                        pattern: block_builder.node(Pattern::If(IfPattern {
                                            pattern: block_builder.node(Pattern::Ignore),
                                            condition: clause,
                                        })),
                                        expr: AstBuilder::from_node(&block)
                                            .node(Expression::Block(block)),
                                    })
                                }
                                Rule::else_block => {
                                    append_else = false;

                                    let block =
                                        if_condition.into_inner().next().unwrap().into_ast();

                                    block_builder.node(MatchCase {
                                        pattern: block_builder.node(Pattern::Ignore),
                                        expr: AstBuilder::from_node(&block)
                                            .node(Expression::Block(block)),
                                    })
                                }
                                k => panic!("unexpected rule within if-else-block: {:?}", k),
                            };

                            cases.push(pattern)
                        }

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

                        ab.node(Block::Match(MatchBlock {
                            subject: make_variable(make_boolean(true, &ab), &ab),
                            cases,
                        }))
                    }
                    Rule::match_block => {
                        let mut match_block = block.into_inner();

                        // firstly get the expresion condition from the match block, the
                        // next rule will be a bunch of match_case rules which can be
                        // converted into ast using the pattern and block implementations...
                        let subject = match_block.next().unwrap().into_ast();
                        let match_cases = match_block.next().unwrap();

                        let mut cases = vec![];

                        for case in match_cases.into_inner() {
                            let case_builder = AstBuilder::from_pair(&case);

                            let ast_case = match case.as_rule() {
                                Rule::match_case => {
                                    let mut components = case.into_inner();

                                    let pattern = components.next().unwrap().into_ast();
                                    let expr = components.next().unwrap().into_ast();

                                    case_builder.node(MatchCase { pattern, expr })
                                }
                                k => panic!("unexpected rule within match_case: {:?}", k),
                            };

                            cases.push(ast_case);
                        }

                        ab.node(Block::Match(MatchBlock { subject, cases }))
                    }
                    Rule::loop_block => {
                        let body_block = block.into_inner().next().unwrap().into_ast();

                        ab.node(Block::Loop(body_block))
                    }
                    Rule::for_block => {
                        let mut for_block = block.into_inner();

                        let pattern: AstNode<Pattern> = for_block.next().unwrap().into_ast();
                        let pat_builder = AstBuilder::from_node(&pattern);

                        let iterator: AstNode<Expression> = for_block.next().unwrap().into_ast();
                        let iter_builder = AstBuilder::from_node(&iterator);

                        let body: AstNode<Block> = for_block.next().unwrap().into_ast();
                        let body_builder = AstBuilder::from_node(&body);

                        ab.node(Block::Loop(ab.node(Block::Match(MatchBlock {
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
                        }))))
                    }
                    Rule::while_block => {
                        let mut while_block = block.into_inner();

                        let condition: AstNode<Expression> = while_block.next().unwrap().into_ast();
                        let condition_builder = AstBuilder::from_node(&condition);

                        let body: AstNode<Block> = while_block.next().unwrap().into_ast();
                        let body_builder = AstBuilder::from_node(&body);

                        ab.node(Block::Loop(ab.node(Block::Match(MatchBlock {
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
                        }))))
                    }
                    Rule::body_block => block.into_ast(),
                    k => panic!("unexpected rule within block variant: {:?}", k),
                }
            }
            Rule::body_block => {
                ab.node(Block::Body(BodyBlock {
                    statements: self.into_inner().map(|p| p.into_ast()).collect(),
                    // @@FIXME: since the tokeniser cannot tell the difference betweeen a statment and an expression (what is returned), we need to do it here...
                    expr: None,
                }))
            }
            k => panic!("unexpected rule within block: {:?}", k),
        }
    }
}

impl IntoAstNode<Statement> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Statement> {
        let ab = AstBuilder::from_pair(&self);

        match self.as_rule() {
            Rule::statement => {
                let statement = self.into_inner().next().unwrap();

                // since we have block statements and semi statements, we can check here
                // to see which path it is, if this is a block statement, we just call
                // into_ast() since there is an implementation for block convetsions
                match statement.as_rule() {
                    Rule::block => ab.node(Statement::Block(statement.into_ast())),
                    Rule::break_st => ab.node(Statement::Break),
                    Rule::continue_st => ab.node(Statement::Continue),
                    Rule::return_st => {
                        let ret_expr = statement.into_inner().next();

                        if let Some(node) = ret_expr {
                            ab.node(Statement::Return(Some(node.into_ast())))
                        } else {
                            ab.node(Statement::Return(None))
                        }
                    }
                    Rule::let_st => {
                        // the first rule will be the pattern which can be automatically converted, whereas
                        // then we have a trait bound and finally an optional expression which is used as an
                        // assignment to the let statement
                        let mut components = statement.into_inner();

                        let pattern = components.next().unwrap().into_ast();

                        let bound_or_value = components.next();
                        let (bound, value) = match bound_or_value {
                            Some(pair) => match pair.as_rule() {
                                Rule::bound => (
                                    Some(pair.into_ast()),
                                    components.next().map(|expr| expr.into_ast()),
                                ),
                                Rule::expr => (None, Some(pair.into_ast())),
                                k => panic!("Unexpected rule within let_st: {:?}", k),
                            },
                            None => (None, None),
                        };

                        ab.node(Statement::Let(LetStatement {
                            pattern,
                            bound,
                            value,
                        }))
                    }
                    Rule::expr_or_assign_st => {
                        let mut components = statement.into_inner().map(|p| p.into_ast());
                        let lhs = components.next().unwrap();

                        // if no rhs is present, this is just an singular expression instead of an
                        // assignment
                        match components.next() {
                            Some(_op) => {
                                // TODO: we need to convert the operator into just a singular one since we
                                // should transpile expressions that use a 're-assignment' operator into
                                // a plain one, for example, `a += 2` should end up as `a = a + 2`...

                                let rhs = components.next().unwrap();
                                ab.node(Statement::Assign(AssignStatement { lhs, rhs }))
                            }
                            None => ab.node(Statement::Expr(lhs)),
                        }
                    }
                    Rule::struct_def => {
                        let mut components = statement.into_inner();
                        let name = components.next().unwrap().into_ast();

                        let bound_or_fields = components.next().unwrap();
                        let mut entries = vec![];

                        let bound = match bound_or_fields.as_rule() {
                            Rule::bound => Some(bound_or_fields.into_ast()),
                            Rule::struct_def_fields => {
                                entries =
                                    bound_or_fields.into_inner().map(|p| p.into_ast()).collect();

                                None
                            }
                            k => panic!("Unexpected rule within struct_def: {:?}", k),
                        };

                        ab.node(Statement::StructDef(StructDef {
                            name,
                            bound,
                            entries,
                        }))
                    }
                    Rule::enum_def => {
                        let mut components = statement.into_inner();
                        let name = components.next().unwrap().into_ast();

                        let bound_or_fields = components.next().unwrap();
                        let mut entries = vec![];

                        let bound = match bound_or_fields.as_rule() {
                            Rule::bound => Some(bound_or_fields.into_ast()),
                            Rule::struct_def_fields => {
                                entries =
                                    bound_or_fields.into_inner().map(|p| p.into_ast()).collect();

                                None
                            }
                            k => panic!("Unexpected rule within enum_def: {:?}", k),
                        };

                        ab.node(Statement::EnumDef(EnumDef {
                            name,
                            bound,
                            entries,
                        }))
                    }
                    Rule::trait_def => {
                        let mut components = statement.into_inner();
                        let name = components.next().unwrap().into_ast();
                        let bound = components.next().unwrap().into_ast();

                        // @@Incomplete: ensure that this is a function_type!!
                        let trait_type = components.next().unwrap().into_ast();

                        ab.node(Statement::TraitDef(TraitDef {
                            name,
                            bound,
                            trait_type,
                        }))
                    }
                    _ => unreachable!(),
                }
            }
            // This rule must be present here because body_block's are made of a
            // arbitrary number of statements, and an optional final expression.
            // So, when we convert the body_blocks' into ast, we don't know if the
            // last item is a statement or expression...
            Rule::expr => ab.node(Statement::Expr(self.into_ast())),
            k => panic!("unexpected rule within statement: {:?}", k),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::*;
    use crate::grammar;
    use pest::Parser;

    use super::*;

    fn parse_input<T>(rule: Rule, input: &str) -> AstNode<T>
    where
        for<'a> HashPair<'a>: IntoAstNode<T>,
    {
        let mut result = grammar::HashParser::parse(rule, input).unwrap();
        let parsed: AstNode<T> = result.next().unwrap().into_ast();
        parsed
    }

    #[test]
    fn test_name() {
        assert_eq!(
            AstNode {
                body: Box::new(Name {
                    string: "universe".to_owned()
                }),
                pos: Location::Span(0, 8,),
                module: 0,
            },
            parse_input::<Name>(Rule::name, "universe"),
        );
    }

    #[test]
    fn test_access_name() {
        assert_eq!(
            AstNode {
                body: Box::new(AccessName {
                    names: vec![
                        AstNode {
                            body: Box::new(Name {
                                string: "iter".to_owned()
                            }),
                            pos: Location::Span(0, 4,),
                            module: 0,
                        },
                        AstNode {
                            body: Box::new(Name {
                                string: "next".to_owned()
                            }),
                            pos: Location::Span(6, 10,),
                            module: 0,
                        },
                        AstNode {
                            body: Box::new(Name {
                                string: "Then".to_owned()
                            }),
                            pos: Location::Span(12, 16,),
                            module: 0,
                        },
                    ],
                }),
                pos: Location::Span(0, 16,),
                module: 0,
            },
            parse_input::<AccessName>(Rule::access_name, "iter::next::Then"),
        );
    }
}
