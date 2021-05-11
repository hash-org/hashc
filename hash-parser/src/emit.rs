use std::iter;

use num::BigInt;

// use crate::IntoAstNode;
use crate::{ast::*, grammar::Rule, location::Location, modules::ModuleIdx};

struct AstBuilder {
    pos: Location,
    module: ModuleIdx,
}

impl AstBuilder {
    pub fn from_pair(pair: &pest::iterators::Pair<'_, Rule>) -> AstBuilder {
        let span = pair.as_span();
        let pos = Location::Span(span.start(), span.end());
        AstBuilder {
            pos,
            module: 0, // @Todo
        }
    }

    #[allow(dead_code)] // @FIXME: temporary to prevent warnings.
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
}

type HashPair<'a> = pest::iterators::Pair<'a, Rule>;

impl IntoAstNode<Name> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Name> {
        match self.as_rule() {
            Rule::name => AstBuilder::from_pair(&self).node(Name {
                string: self.as_str().to_owned(),
            }),
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
        match self.as_rule() {
            Rule::literal_expr => {
                let ab = AstBuilder::from_pair(&self);
                let in_expr = self.into_inner().next().unwrap();
                match in_expr.as_rule() {
                    Rule::integer_literal => {
                        let inner = in_expr.into_inner().next().unwrap();
                        // this could be binary, hex, octal or decimal...
                        match inner.as_rule() {
                            Rule::decimal_literal => {
                                // check if there is a float exp component since we allow this, although if the specified exponent is
                                // float, we'll cast the result to decimal...
                                let mut components = inner.into_inner();
                                let num = components.next().unwrap();

                                let val = BigInt::parse_bytes(num.as_str().as_bytes(), 10).unwrap();

                                // @@Correctness: maybe this shouldn't happen and we should make a
                                //                float from the given number?
                                if let Some(l) = components.next() {
                                    let exp = u32::from_str_radix(l.as_str(), 10).unwrap();
                                    val.pow(exp);
                                }

                                ab.node(Literal::Int(val))
                            }
                            Rule::hex_literal => {
                                let val =
                                    BigInt::parse_bytes(inner.as_str().as_bytes(), 16).unwrap();
                                ab.node(Literal::Int(val))
                            }
                            Rule::octal_literal => {
                                let val =
                                    BigInt::parse_bytes(inner.as_str().as_bytes(), 8).unwrap();
                                ab.node(Literal::Int(val))
                            }
                            Rule::bin_literal => {
                                let val =
                                    BigInt::parse_bytes(inner.as_str().as_bytes(), 2).unwrap();
                                ab.node(Literal::Int(val))
                            }
                            _ => unreachable!(),
                        }
                    }
                    Rule::float_literal => unimplemented!(),
                    Rule::char_literal => {
                        let c: char = in_expr.as_span().as_str().chars().next().unwrap();
                        ab.node(Literal::Char(c))
                    }
                    Rule::string_literal => {
                        let s = String::from(in_expr.as_span().as_str());
                        ab.node(Literal::Str(s))
                    }
                    Rule::list_literal => {
                        // since list literals are just a bunch of expressions, we just call
                        // into_ast() on each member and collect at the end
                        let elements = in_expr.into_inner().map(|p| p.into_ast()).collect();

                        ab.node(Literal::List(ListLiteral { elements }))
                    }
                    Rule::set_literal => {
                        // since set literals are just a bunch of expressions, we just call
                        // into_ast() on each member and collect at the end
                        let elements = in_expr.into_inner().map(|p| p.into_ast()).collect();

                        ab.node(Literal::Set(SetLiteral { elements }))
                    }
                    Rule::tuple_literal => {
                        // since tuple literals are just a bunch of expressions, we just call
                        // into_ast() on each member and collect at the end
                        let elements = in_expr.into_inner().map(|p| p.into_ast()).collect();

                        ab.node(Literal::Tuple(TupleLiteral { elements }))
                    }
                    Rule::map_literal => {
                        // A map is made of a vector of 'map_entries' rules, which are just two
                        // expressions.
                        let elements = in_expr
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
                        let mut components = in_expr.into_inner();

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
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<LiteralPattern> for HashPair<'_> {
    fn into_ast(self) -> AstNode<LiteralPattern> {
        // match self.as_rule() {
        //
        // }
        unimplemented!()
    }
}

impl IntoAstNode<Pattern> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Pattern> {
        // match self.as_rule() {
        //
        // }
        unimplemented!()
    }
}

impl IntoAstNode<Expression> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Expression> {
        match self.as_rule() {
            Rule::expr => {
                let ab = AstBuilder::from_pair(&self);
                let expr = self.into_inner().next().unwrap();

                match expr.as_rule() {
                    Rule::block => ab.node(Expression::Block(expr.into_ast())),
                    Rule::struct_literal => ab.node(Expression::LiteralExpr(expr.into_ast())),
                    Rule::binary_expr => {
                        // now this is a bitch because we have o
                        unimplemented!()
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }
}

impl IntoAstNode<Block> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Block> {
        // match self.as_rule() {
        //
        // }
        unimplemented!()
    }
}

impl IntoAstNode<Statement> for HashPair<'_> {
    fn into_ast(self) -> AstNode<Statement> {
        match self.as_rule() {
            Rule::statement => {
                let ab = AstBuilder::from_pair(&self);
                let statement = self.into_inner().next().unwrap();

                // since we have block statements and semi statements, we can check here
                // to see which path it is, if this is a block statement, we just call
                // into_ast() since there is an implementation for block convetsions
                match statement.as_rule() {
                    Rule::block_st => statement.into_ast(),
                    Rule::break_st => ab.node(Statement::Break),
                    Rule::continue_st => ab.node(Statement::Continue),
                    Rule::return_st => unimplemented!(),
                    Rule::let_st => unimplemented!(),
                    Rule::expr_or_assign_st => {
                        let mut items = statement.into_inner().map(|p| p.into_ast());
                        let lhs = items.next().unwrap();

                        // if no rhs is present, this is just an singular expression instead of an
                        // assignment
                        match items.next() {
                            Some(rhs) => ab.node(Statement::Assign(AssignStatement { lhs, rhs })),
                            None => ab.node(Statement::Expr(lhs)),
                        }
                    }
                    Rule::struct_def => {
                        unimplemented!()
                    }
                    Rule::enum_def => {
                        unimplemented!()
                    }
                    Rule::trait_def => {
                        unimplemented!()
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
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
