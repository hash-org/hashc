use crate::grammar::Rule;

pub enum OperatorFunction {
    Named(&'static str),
    LazyNamed(&'static str),
    Leq,
    Geq,
    Lt,
    Gt,
}

/// Function to convert a pest rule denoting operators into a named function symbols
/// that represent their function call, more details about names of functions is
/// accessible in the docs at "https://hash-org.github.io/lang/basics/operators.html"
pub fn convert_rule_into_fn_call(rule: &Rule) -> Option<OperatorFunction> {
    use OperatorFunction::*;

    match rule {
        Rule::assign_eq_op => None,
        Rule::add_eq_op => Some(Named("add_eq")),
        Rule::sub_eq_op => Some(Named("sub_eq")),
        Rule::div_eq_op => Some(Named("div_eq")),
        Rule::mod_eq_op => Some(Named("mod_eq")),
        Rule::andl_eq_op => Some(Named("and_eq")),
        Rule::orl_eq_op => Some(Named("or_eq")),
        Rule::andb_eq_op => Some(Named("andb_eq")),
        Rule::orb_eq_op => Some(Named("orb_eq")),
        Rule::xorb_eq_op => Some(Named("xorb_eq")),

        // non-update operators
        Rule::double_eq_op => Some(Named("eq")),
        Rule::neq_op => Some(Named("not")),
        Rule::add_op => Some(Named("add")),
        Rule::sub_op => Some(Named("sub")),
        Rule::mul_op => Some(Named("mul")),
        Rule::div_op => Some(Named("div")),
        Rule::mod_op => Some(Named("mod")),
        Rule::andl_op => Some(LazyNamed("and")),
        Rule::orl_op => Some(LazyNamed("or")),
        Rule::shl_op => Some(Named("shl")),
        Rule::shr_op => Some(Named("shr")),
        Rule::exp_op => Some(Named("exp")),
        Rule::geq_op => Some(Geq),
        Rule::leq_op => Some(Leq),
        Rule::gt_op => Some(Gt),
        Rule::lt_op => Some(Lt),
        Rule::andb_op => Some(Named("andb")),
        Rule::orb_op => Some(Named("orb")),
        Rule::xorb_op => Some(Named("xorb")),
        k => panic!("Unexpected rule within assignment_operator: {:?}", k),
    }
}
