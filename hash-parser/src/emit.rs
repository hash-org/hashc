use std::iter;

// use crate::ast::IntoAstNode;
use crate::{
    ast::{self},
    grammar::Rule,
    location::Location,
    modules::ModuleIdx,
};

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
    pub fn from_node<T>(node: &ast::AstNode<T>) -> AstBuilder {
        AstBuilder {
            pos: node.pos,
            module: node.module,
        }
    }

    pub fn node<T>(&self, inner: T) -> ast::AstNode<T> {
        ast::AstNode {
            body: Box::new(inner),
            pos: self.pos,
            module: self.module,
        }
    }
}

type HashPair<'a> = pest::iterators::Pair<'a, Rule>;

impl ast::IntoAstNode<ast::Name> for HashPair<'_> {
    fn into_ast(self) -> ast::AstNode<ast::Name> {
        match self.as_rule() {
            Rule::name => AstBuilder::from_pair(&self).node(ast::Name {
                string: self.as_str().to_owned(),
            }),
            _ => unreachable!(),
        }
    }
}

impl ast::IntoAstNode<ast::AccessName> for HashPair<'_> {
    fn into_ast(self) -> ast::AstNode<ast::AccessName> {
        match self.as_rule() {
            Rule::access_name => AstBuilder::from_pair(&self).node(ast::AccessName {
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

fn single_access_name(ab: &AstBuilder, name: &str) -> ast::AstNode<ast::AccessName> {
    ab.node(ast::AccessName {
        names: vec![ab.node(ast::Name {
            string: name.to_owned(),
        })],
    })
}

impl ast::IntoAstNode<ast::Type> for HashPair<'_> {
    fn into_ast(self) -> ast::AstNode<ast::Type> {
        match self.as_rule() {
            Rule::any_type => {
                let ab = AstBuilder::from_pair(&self);
                let in_type = self.into_inner().next().unwrap();
                match in_type.as_rule() {
                    Rule::infer_type => ab.node(ast::Type::Infer),
                    Rule::named_type => {
                        let mut in_named = in_type.into_inner();

                        let name = in_named.next().unwrap().into_ast();
                        let type_args = in_named
                            .next()
                            .map(|n| n.into_inner().map(|p| p.into_ast()).collect())
                            .unwrap_or(vec![]);

                        ab.node(ast::Type::Named(ast::NamedType { name, type_args }))
                    }
                    Rule::fn_type => {
                        let mut in_func = in_type.into_inner();

                        let args = in_func.next().unwrap().into_inner().map(|p| p.into_ast());
                        let ret = in_func.next().unwrap().into_ast();

                        let args_ret = args.chain(iter::once(ret));
                        ab.node(ast::Type::Named(ast::NamedType {
                            name: single_access_name(&ab, FUNCTION_TYPE_NAME),
                            type_args: args_ret.collect(),
                        }))
                    }
                    Rule::tuple_type => {
                        let inner = in_type.into_inner().map(|p| p.into_ast());

                        ab.node(ast::Type::Named(ast::NamedType {
                            name: single_access_name(&ab, TUPLE_TYPE_NAME),
                            type_args: inner.collect(),
                        }))
                    }
                    Rule::list_type => {
                        let inner = in_type.into_inner().map(|p| p.into_ast());

                        // list type should only have one type
                        debug_assert_eq!(inner.size_hint().0, 1);

                        ab.node(ast::Type::Named(ast::NamedType {
                            name: single_access_name(&ab, LIST_TYPE_NAME),
                            type_args: inner.collect(),
                        }))
                    }
                    Rule::set_type => {
                        let inner = in_type.into_inner().map(|p| p.into_ast());

                        // set type should only have one type
                        debug_assert_eq!(inner.size_hint().0, 1);

                        ab.node(ast::Type::Named(ast::NamedType {
                            name: single_access_name(&ab, SET_TYPE_NAME),
                            type_args: inner.collect(),
                        }))
                    }
                    Rule::map_type => {
                        let inner = in_type.into_inner().map(|p| p.into_ast());

                        // map type should only have a type for a key and a value
                        debug_assert_eq!(inner.size_hint().0, 2);

                        ab.node(ast::Type::Named(ast::NamedType {
                            name: single_access_name(&ab, MAP_TYPE_NAME),
                            type_args: inner.collect(),
                        }))
                    }
                    Rule::existential_type => ab.node(ast::Type::Existential),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }
}

impl ast::IntoAstNode<ast::Literal> for HashPair<'_> {
    fn into_ast(self) -> ast::AstNode<ast::Literal> {
        match self.as_rule() {
            _ => unimplemented!(),
        }
    }
}

impl ast::IntoAstNode<ast::LiteralPattern> for HashPair<'_> {
    fn into_ast(self) -> ast::AstNode<ast::LiteralPattern> {
        match self.as_rule() {
            _ => unimplemented!(),
        }
    }
}

impl ast::IntoAstNode<ast::Pattern> for HashPair<'_> {
    fn into_ast(self) -> ast::AstNode<ast::Pattern> {
        match self.as_rule() {
            _ => unimplemented!(),
        }
    }
}

impl ast::IntoAstNode<ast::Expression> for HashPair<'_> {
    fn into_ast(self) -> ast::AstNode<ast::Expression> {
        match self.as_rule() {
            _ => unimplemented!(),
        }
    }
}

impl ast::IntoAstNode<ast::Block> for HashPair<'_> {
    fn into_ast(self) -> ast::AstNode<ast::Block> {
        match self.as_rule() {
            _ => unimplemented!(),
        }
    }
}

impl ast::IntoAstNode<ast::Statement> for HashPair<'_> {
    fn into_ast(self) -> ast::AstNode<ast::Statement> {
        match self.as_rule() {
            _ => unimplemented!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{AccessName, AstNode, IntoAstNode, Name};
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
