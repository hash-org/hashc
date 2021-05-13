//! Emit precedence climber definitions for PEST front end.
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::grammar::Rule;
use crate::{ast::*, emit::AstBuilder};

use pest::{
    iterators::Pair,
    prec_climber::{Assoc, Operator, PrecClimber},
};

lazy_static! {
    pub static ref PREC_CLIMBER: PrecClimber<Rule> = build_precedence_climber();
}

fn build_precedence_climber() -> PrecClimber<Rule> {
    PrecClimber::new(vec![
        Operator::new(Rule::orl_op, Assoc::Left),
        Operator::new(Rule::andl_op, Assoc::Left),
        Operator::new(Rule::double_eq_op, Assoc::Right) | Operator::new(Rule::neq_op, Assoc::Right),
        Operator::new(Rule::geq_op, Assoc::Left)
            | Operator::new(Rule::leq_op, Assoc::Left)
            | Operator::new(Rule::gt_op, Assoc::Left)
            | Operator::new(Rule::lt_op, Assoc::Left),
        Operator::new(Rule::xorb_op, Assoc::Left) | Operator::new(Rule::orb_op, Assoc::Left),
        Operator::new(Rule::andb_op, Assoc::Left),
        Operator::new(Rule::shr_op, Assoc::Left) | Operator::new(Rule::shl_op, Assoc::Left),
        Operator::new(Rule::add_op, Assoc::Left) | Operator::new(Rule::sub_op, Assoc::Left),
        Operator::new(Rule::mod_op, Assoc::Left)
            | Operator::new(Rule::div_op, Assoc::Left)
            | Operator::new(Rule::mul_op, Assoc::Left),
        Operator::new(Rule::exp_op, Assoc::Right),
    ])
}

fn build_binary(
    lhs: AstNode<Expression>,
    op: Pair<'_, Rule>,
    rhs: AstNode<Expression>,
) -> AstNode<Expression> {
    let ab = AstBuilder::from_pair(&op);

    let subject_name = String::from(match op.as_rule() {
        Rule::triple_eq_op => "ref_eq",
        Rule::double_eq_op => "eq",
        Rule::double_neq_op => "ref_not_eq",
        Rule::neq_op => "logical_not",
        Rule::add_op => "add",
        Rule::sub_op => "sub",
        Rule::mul_op => "mul",
        Rule::div_op => "div",
        Rule::mod_op => "mod",
        Rule::andl_op => "logical_and",
        Rule::orl_op => "logical_or",
        Rule::shl_op => "left_shift",
        Rule::shr_op => "right_shift",
        Rule::exp_op => "exp",
        Rule::geq_op => "gt_eq",
        Rule::leq_op => "lt_eq",
        Rule::gt_op => "gt",
        Rule::lt_op => "lt",
        Rule::andb_op => "bit_and",
        Rule::orb_op => "bit_or",
        Rule::xorb_op => "bit_xor",
        _ => unreachable!(),
    });

    ab.node(Expression::FunctionCall(FunctionCallExpr {
        subject: ab.node(Expression::Variable(VariableExpr {
            name: ab.node(AccessName {
                names: vec![ab.node(Name {
                    string: subject_name,
                })],
            }),
            type_args: vec![], // we dont need any kind of typeargs since were just transpilling here
        })),
        args: ab.node(FunctionCallArgs {
            entries: vec![lhs, rhs],
        }),
    }))
}

pub fn climb(pair: Pair<'_, Rule>) -> AstNode<Expression> {
    PREC_CLIMBER.climb(pair.into_inner(), |pair| pair.into_ast(), build_binary)
}
