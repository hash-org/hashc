use crate::grammar::Rule;

/// Function to convert a pest rule denoting operators into a named function symbols
/// that represent their function call, more details about names of functions is
/// accessible in the docs at "https://hash-org.github.io/lang/basics/operators.html"
pub fn convert_rule_into_fn_call(rule: &Rule) -> Option<&'static str> {
    match rule {
        Rule::assign_eq_op => None,
        Rule::add_eq_op => Some("pos"),
        Rule::sub_eq_op => Some("neg"),
        Rule::div_eq_op => Some("div"),
        Rule::mod_eq_op => Some("mod"),
        Rule::andl_eq_op => Some("andl"),
        Rule::orl_eq_op => Some("orl"),
        Rule::andb_eq_op => Some("andb"),
        Rule::orb_eq_op => Some("orb"),
        Rule::xorb_eq_op => Some("xorb"),

        // non-update operators
        Rule::triple_eq_op => Some("ref_eq"),
        Rule::double_eq_op => Some("eq"),
        Rule::double_neq_op => Some("ref_neq"),
        Rule::neq_op => Some("logical_not"),
        Rule::add_op => Some("add"),
        Rule::sub_op => Some("sub"),
        Rule::mul_op => Some("mul"),
        Rule::div_op => Some("div"),
        Rule::mod_op => Some("mod"),
        Rule::andl_op => Some("logical_and"),
        Rule::orl_op => Some("logical_or"),
        Rule::shl_op => Some("left_shift"),
        Rule::shr_op => Some("right_shift"),
        Rule::exp_op => Some("exp"),
        Rule::geq_op => Some("gt_eq"),
        Rule::leq_op => Some("lt_eq"),
        Rule::gt_op => Some("gt"),
        Rule::lt_op => Some("lt"),
        Rule::andb_op => Some("bit_and"),
        Rule::orb_op => Some("bit_or"),
        Rule::xorb_op => Some("bit_xor"),
        k => panic!("Unexpected rule within assignment_operator: {:?}", k),
    }
}
