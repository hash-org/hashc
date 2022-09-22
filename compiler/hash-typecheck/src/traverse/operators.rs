use hash_ast::ast::{AstNodeRef, BinOp, ParamOrigin};
use hash_source::identifier::{Identifier, CORE_IDENTIFIERS};
use hash_types::terms::TermId;

use super::visitor::TcVisitor;
use crate::{diagnostics::error::TcResult, ops::AccessToOps};

impl<'tc> TcVisitor<'tc> {
    /// Creates the basic type which is resultant from an [BinOp]. This
    /// operation is required for primitive and non-primitive types.
    pub(crate) fn create_operator_fn(
        &self,
        lhs: TermId,
        rhs: TermId,
        op: AstNodeRef<BinOp>,
        assigning: bool,
    ) -> TermId {
        let bin_op = *op.body();
        let trt_name = self.convert_bin_op_into_trt_name(bin_op, assigning);

        let prop_access = self.builder().create_prop_access(lhs, trt_name);
        self.copy_location_from_node_to_target(op, prop_access);

        let builder = self.builder();
        builder.create_fn_call_term(
            prop_access,
            builder.create_args([builder.create_nameless_arg(rhs)], ParamOrigin::Fn),
        )
    }

    /// This creates the appropriate type for a lazy (short-circuiting) operator
    /// such as the logical `and` and `or` operators. These [BinOp]s have
    /// differing requirements in the way they are evaluated by those
    /// functions, this is why `create_operator_fn` cannot be used for these
    /// operators.
    pub(crate) fn create_lazy_operator_fn(
        &self,
        lhs: TermId,
        rhs: TermId,
        op: BinOp,
    ) -> TcResult<TermId> {
        let trt_name = match op {
            BinOp::And => "and",
            BinOp::Or => "or",
            // All other operators are not lazy and thus should not be used here...
            _ => unreachable!(),
        };

        let lhs_ty = self.typer().infer_ty_of_term(lhs)?;
        let rhs_ty = self.typer().infer_ty_of_term(rhs)?;

        let builder = self.builder();

        // () => lhs
        let fn_ty = builder.create_fn_ty_term(builder.create_params([], ParamOrigin::Fn), lhs_ty);
        let lhs = builder.create_fn_lit_term(fn_ty, lhs);

        // () => rhs
        let fn_ty = builder.create_fn_ty_term(builder.create_params([], ParamOrigin::Fn), rhs_ty);
        let rhs = builder.create_fn_lit_term(fn_ty, rhs);

        // (() => lhs).trait_name()
        let prop_access = builder.create_prop_access(lhs, trt_name);

        // (() => lhs).trait_name(() => rhs)
        Ok(builder.create_fn_call_term(
            prop_access,
            builder.create_args([builder.create_nameless_arg(rhs)], ParamOrigin::Fn),
        ))
    }

    /// Convert a [BinOp] into the appropriate trait name symbol. This function
    /// also takes into account whether or not this operator is assigning. Some
    /// [BinOp]s don't have assigning variants which means that  `assigning`
    /// flag is ignored when it does not make a difference.
    ///
    /// ##Panics
    ///
    /// - If the passed [BinOp] has no trait name equivalent, these [BinOp]s are
    /// either [BinOp::As] or [BinOp::Merge].
    fn convert_bin_op_into_trt_name(&self, op: BinOp, assigning: bool) -> Identifier {
        match (op, assigning) {
            // Equality, ordering operators don't have assigning variants
            // so no need to handle this case
            (BinOp::EqEq, _) => CORE_IDENTIFIERS.trt_eq,
            (BinOp::NotEq, _) => CORE_IDENTIFIERS.trt_neq,
            (BinOp::Gt, _) => CORE_IDENTIFIERS.trt_gt,
            (BinOp::GtEq, _) => CORE_IDENTIFIERS.trt_gt_eq,
            (BinOp::Lt, _) => CORE_IDENTIFIERS.trt_lt,
            (BinOp::LtEq, _) => CORE_IDENTIFIERS.trt_lt_eq,

            // Lazy operators don't have assigning variants
            (BinOp::Or, _) => CORE_IDENTIFIERS.trt_or,
            (BinOp::And, _) => CORE_IDENTIFIERS.trt_and,

            // Arithmetic operators
            (BinOp::BitOr, true) => CORE_IDENTIFIERS.trt_bit_or_eq,
            (BinOp::BitOr, false) => CORE_IDENTIFIERS.trt_bit_or,
            (BinOp::BitAnd, true) => CORE_IDENTIFIERS.trt_bit_and_eq,
            (BinOp::BitAnd, false) => CORE_IDENTIFIERS.trt_bit_and,
            (BinOp::BitXor, true) => CORE_IDENTIFIERS.trt_bit_xor_eq,
            (BinOp::BitXor, false) => CORE_IDENTIFIERS.trt_bit_xor,
            (BinOp::Exp, true) => CORE_IDENTIFIERS.trt_bit_exp_eq,
            (BinOp::Exp, false) => CORE_IDENTIFIERS.trt_bit_exp,
            (BinOp::Shr, true) => CORE_IDENTIFIERS.trt_shr_eq,
            (BinOp::Shr, false) => CORE_IDENTIFIERS.trt_shr,
            (BinOp::Shl, true) => CORE_IDENTIFIERS.trt_shl_eq,
            (BinOp::Shl, false) => CORE_IDENTIFIERS.trt_shl,
            (BinOp::Add, true) => CORE_IDENTIFIERS.trt_add_eq,
            (BinOp::Add, false) => CORE_IDENTIFIERS.trt_add,
            (BinOp::Sub, true) => CORE_IDENTIFIERS.trt_sub,
            (BinOp::Sub, false) => CORE_IDENTIFIERS.trt_sub_eq,
            (BinOp::Mul, true) => CORE_IDENTIFIERS.trt_mul_eq,
            (BinOp::Mul, false) => CORE_IDENTIFIERS.trt_mul,
            (BinOp::Div, true) => CORE_IDENTIFIERS.trt_div_eq,
            (BinOp::Div, false) => CORE_IDENTIFIERS.trt_div,
            (BinOp::Mod, true) => CORE_IDENTIFIERS.trt_mod_eq,
            (BinOp::Mod, false) => CORE_IDENTIFIERS.trt_mod,

            // These should be dealt with before or completely erased at this
            // point.
            (BinOp::Merge | BinOp::As, _) => unreachable!(),
        }
    }
}
