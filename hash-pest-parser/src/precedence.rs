//! Emit precedence climber definitions for PEST front end.
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::grammar::HashPair;
use crate::grammar::Rule;
use crate::utils::convert_rule_into_fn_call;
use hash_ast::ast::*;
use hash_ast::error::ParseResult;
use hash_ast::parse::ModuleResolver;
use lazy_static::lazy_static;

use pest::prec_climber::{Assoc, Operator, PrecClimber};

lazy_static! {
    pub static ref PREC_CLIMBER: PrecClimber<Rule> = build_precedence_climber();
}

fn build_precedence_climber() -> PrecClimber<Rule> {
    PrecClimber::new(vec![
        Operator::new(Rule::orl_op, Assoc::Left),
        Operator::new(Rule::andl_op, Assoc::Left),
        Operator::new(Rule::double_eq_op, Assoc::Right)
            | Operator::new(Rule::neq_op, Assoc::Right),
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
