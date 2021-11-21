use std::borrow::Cow;

use hash_ast::operator::{CompoundFn, OperatorFn};

use crate::grammar::Rule;

/// Function to convert a pest rule denoting operators into a named function symbols
/// that represent their function call, more details about names of functions is
/// accessible in the docs at "https://hash-org.github.io/lang/basics/operators.html"
impl From<Rule> for Option<OperatorFn> {
    fn from(rule: Rule) -> Self {
        use OperatorFn::*;

        match rule {
            // special case of just the assignment operator
            Rule::assign_eq_op => None,

            // assigning operators, ones that will overwrite the lhs of the expression
            // with a new value. This is important since it needs to have different
            // traits and handled differently using references...
            Rule::add_eq_op => Some(Named {
                name: Cow::Borrowed("add_eq"),
                assigning: true,
            }),
            Rule::sub_eq_op => Some(Named {
                name: Cow::Borrowed("sub_eq"),
                assigning: true,
            }),
            Rule::div_eq_op => Some(Named {
                name: Cow::Borrowed("div_eq"),
                assigning: true,
            }),
            Rule::mod_eq_op => Some(Named {
                name: Cow::Borrowed("mod_eq"),
                assigning: true,
            }),
            Rule::mul_eq_op => Some(Named {
                name: Cow::Borrowed("mul_eq"),
                assigning: true,
            }),
            Rule::andl_eq_op => Some(LazyNamed {
                name: Cow::Borrowed("and_eq"),
                assigning: true,
            }),
            Rule::orl_eq_op => Some(LazyNamed {
                name: Cow::Borrowed("or_eq"),
                assigning: true,
            }),
            Rule::andb_eq_op => Some(Named {
                name: Cow::Borrowed("andb_eq"),
                assigning: true,
            }),
            Rule::orb_eq_op => Some(Named {
                name: Cow::Borrowed("orb_eq"),
                assigning: true,
            }),
            Rule::exp_eq_op => Some(Named {
                name: Cow::Borrowed("exp_eq"),
                assigning: true,
            }),
            Rule::xorb_eq_op => Some(Named {
                name: Cow::Borrowed("xorb_eq"),
                assigning: true,
            }),

            // non-assigning operators
            Rule::double_eq_op => Some(Named {
                name: Cow::Borrowed("eq"),
                assigning: false,
            }),
            Rule::neq_op => Some(Named {
                name: Cow::Borrowed("not_eq"),
                assigning: false,
            }),
            Rule::add_op => Some(Named {
                name: Cow::Borrowed("add"),
                assigning: false,
            }),
            Rule::sub_op => Some(Named {
                name: Cow::Borrowed("sub"),
                assigning: false,
            }),
            Rule::mul_op => Some(Named {
                name: Cow::Borrowed("mul"),
                assigning: false,
            }),
            Rule::div_op => Some(Named {
                name: Cow::Borrowed("div"),
                assigning: false,
            }),
            Rule::mod_op => Some(Named {
                name: Cow::Borrowed("mod"),
                assigning: false,
            }),
            Rule::andl_op => Some(LazyNamed {
                name: Cow::Borrowed("and"),
                assigning: false,
            }),
            Rule::orl_op => Some(LazyNamed {
                name: Cow::Borrowed("or"),
                assigning: false,
            }),
            Rule::shl_op => Some(Named {
                name: Cow::Borrowed("shl"),
                assigning: false,
            }),
            Rule::shr_op => Some(Named {
                name: Cow::Borrowed("shr"),
                assigning: false,
            }),
            Rule::exp_op => Some(Named {
                name: Cow::Borrowed("exp"),
                assigning: false,
            }),
            Rule::andb_op => Some(Named {
                name: Cow::Borrowed("andb"),
                assigning: false,
            }),
            Rule::orb_op => Some(Named {
                name: Cow::Borrowed("orb"),
                assigning: false,
            }),
            Rule::xorb_op => Some(Named {
                name: Cow::Borrowed("xorb"),
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
}
