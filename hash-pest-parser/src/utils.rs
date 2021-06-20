use crate::grammar::Rule;

pub enum CompoundFn {
    Leq,
    Geq,
    Lt,
    Gt,
}

pub enum OperatorFn {
    Named { name: &'static str, assigning: bool },
    LazyNamed { name: &'static str, assigning: bool },
    Compound { name: CompoundFn, assigning: bool },
}

/// Function to convert a pest rule denoting operators into a named function symbols
/// that represent their function call, more details about names of functions is
/// accessible in the docs at "https://hash-org.github.io/lang/basics/operators.html"
pub fn convert_rule_into_fn_call(rule: &Rule) -> Option<OperatorFn> {
    use OperatorFn::*;

    match rule {
        // special case of just the assignment operator
        Rule::assign_eq_op => None,

        // assinging operators, ones that will overwrite the lhs of the expression
        // with a new value. This is important since it needs to have different
        // traits and handeled differently using references...
        Rule::add_eq_op => Some(Named {
            name: "add_eq",
            assigning: true,
        }),
        Rule::sub_eq_op => Some(Named {
            name: "sub_eq",
            assigning: true,
        }),
        Rule::div_eq_op => Some(Named {
            name: "div_eq",
            assigning: true,
        }),
        Rule::mod_eq_op => Some(Named {
            name: "mod_eq",
            assigning: true,
        }),
        Rule::mul_eq_op => Some(Named {
            name: "mul_eq",
            assigning: true,
        }),
        Rule::andl_eq_op => Some(LazyNamed {
            name: "and_eq",
            assigning: true,
        }),
        Rule::orl_eq_op => Some(LazyNamed {
            name: "or_eq",
            assigning: true,
        }),
        Rule::andb_eq_op => Some(Named {
            name: "andb_eq",
            assigning: true,
        }),
        Rule::orb_eq_op => Some(Named {
            name: "orb_eq",
            assigning: true,
        }),
        Rule::xorb_eq_op => Some(Named {
            name: "xorb_eq",
            assigning: true,
        }),

        // non-assigning operators
        Rule::double_eq_op => Some(Named {
            name: "eq",
            assigning: false,
        }),
        Rule::neq_op => Some(Named {
            name: "not_eq",
            assigning: false,
        }),
        Rule::add_op => Some(Named {
            name: "add",
            assigning: false,
        }),
        Rule::sub_op => Some(Named {
            name: "sub",
            assigning: false,
        }),
        Rule::mul_op => Some(Named {
            name: "mul",
            assigning: false,
        }),
        Rule::div_op => Some(Named {
            name: "div",
            assigning: false,
        }),
        Rule::mod_op => Some(Named {
            name: "mod",
            assigning: false,
        }),
        Rule::andl_op => Some(LazyNamed {
            name: "and",
            assigning: false,
        }),
        Rule::orl_op => Some(LazyNamed {
            name: "or",
            assigning: false,
        }),
        Rule::shl_op => Some(Named {
            name: "shl",
            assigning: false,
        }),
        Rule::shr_op => Some(Named {
            name: "shr",
            assigning: false,
        }),
        Rule::exp_op => Some(Named {
            name: "exp",
            assigning: false,
        }),
        Rule::andb_op => Some(Named {
            name: "andb",
            assigning: false,
        }),
        Rule::orb_op => Some(Named {
            name: "orb",
            assigning: false,
        }),
        Rule::xorb_op => Some(Named {
            name: "xorb",
            assigning: false,
        }),

        // Compound functions that require further simplification
        Rule::geq_op => Some(Compound {
            name: CompoundFn::Geq,
            assigning: false,
        }),
        Rule::leq_op => Some(Compound {
            name: CompoundFn::Leq,
            assigning: false,
        }),
        Rule::gt_op => Some(Compound {
            name: CompoundFn::Gt,
            assigning: false,
        }),
        Rule::lt_op => Some(Compound {
            name: CompoundFn::Lt,
            assigning: false,
        }),

        k => panic!("Unexpected rule within assignment_operator: {:?}", k),
    }
}
