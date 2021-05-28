//! Emit precedence climber definitions for PEST front end.
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::utils::convert_rule_into_fn_call;
use crate::{ast::*, emit::AstBuilder};
use crate::{grammar::Rule, modules::ModuleResolver};

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

    // Panic here if we cannot convert the operator into a function call
    let subject_name = convert_rule_into_fn_call(&op.as_rule()).unwrap_or_else(|| unreachable!());

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

pub fn climb(pair: Pair<'_, Rule>, resolver: &ModuleResolver) -> AstNode<Expression> {
    PREC_CLIMBER.climb(
        pair.into_inner(),
        |pair| pair.into_ast(resolver),
        build_binary,
    )
}
