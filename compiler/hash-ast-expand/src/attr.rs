//! Any logic related with attribute checking.

use hash_ast::ast;
use hash_attrs::{
    attr::{attr_store, Attr, AttrArgIdx, AttrValue, AttrValueKind, Attrs},
    target::{AttrNode, AttrTarget},
    ty::ATTR_MAP,
};
use hash_reporting::diagnostic::DiagnosticsMut;
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    TrivialSequenceStoreKey,
};
use hash_tir::{
    args::Arg,
    environment::stores::tir_stores,
    lits::{CharLit, FloatLit, IntLit, Lit, StrLit},
    params::ParamIndex,
    primitives::primitives,
    terms::Term,
    tys::{Ty, TyId},
    utils::params::ParamUtils,
};

use crate::{
    diagnostics::{
        error::{ExpansionError, ExpansionErrorKind},
        warning::ExpansionWarning,
    },
    visitor::AstExpander,
};

impl AstExpander {
    /// Make a [ParamUtils].
    fn param_utils(&self) -> ParamUtils {
        ParamUtils
    }

    pub fn check_macro_invocations(
        &mut self,
        node: ast::AstNodeRef<ast::MacroInvocations>,
        subject: AttrNode<'_>,
    ) {
        // If the macro invocation is correct, then we can append
        // all of the attributes that are being applied onto the
        // the target.
        let mut attrs = Attrs::with_capacity(node.body.invocations.len());
        let id = subject.id();

        for invocation in node.invocations.iter() {
            let maybe_attr = self.try_create_attr_from_macro(invocation.ast_ref(), subject);

            // Create a new attribute checker, and check that the attribute
            // is valid.
            if let Some(attr) = maybe_attr && self.check_attrs(&attrs, &attr, subject) {
                attrs.add_attr(attr);
            }
        }

        attr_store().insert(id, attrs);
    }

    /// Check that the attribute argument type matches the expected parameter
    /// type which is registered in [hash_attrs::ty::ATTR_MAP]. If the types
    /// mismatch, the function emits an error, and returns false.
    fn check_attr_arg_and_param_tys_match(
        &mut self,
        attr: &Attr,
        target: AttrArgIdx,
        param_ty: TyId,
    ) -> bool {
        let arg = attr.get_arg(target).unwrap();
        let value = arg.value;

        let mut maybe_emit_err = |matches: bool| {
            if !matches {
                self.diagnostics.add_error(ExpansionError::new(
                    ExpansionErrorKind::InvalidAttributeArgTy {
                        name: attr.name,
                        target,
                        value,
                        ty: param_ty,
                    },
                    arg.origin,
                ));
            }

            matches
        };

        match param_ty.value() {
            Ty::Data(data) => match data.data_def {
                d if d == primitives().i32() => {
                    maybe_emit_err(matches!(value, AttrValueKind::Int(_)))
                }
                d if d == primitives().f64() => {
                    maybe_emit_err(matches!(value, AttrValueKind::Float(_)))
                }
                d if d == primitives().char() => {
                    maybe_emit_err(matches!(value, AttrValueKind::Char(_)))
                }
                d if d == primitives().str() => {
                    maybe_emit_err(matches!(value, AttrValueKind::Str(_)))
                }
                _ => panic!("unexpected attribute parameter type"),
            },
            _ => panic!("unexpected attribute parameter type"),
        }
    }

    /// Check a macro attribute invocation based on the kind of macro that was
    /// invoked.
    pub fn try_create_attr_from_macro(
        &mut self,
        node: ast::AstNodeRef<ast::MacroInvocation>,
        subject: AttrNode<'_>,
    ) -> Option<Attr> {
        // @@Temporary: since we don't fully support macros yet, we're checking within
        // the attributes that are currently builtin for all of the available
        // macros, if they don't exist, then we emit an error.
        let macro_name = node.name.ident;

        // Try to look this up in the ATTR_MAP
        if let Some(attr_id) = ATTR_MAP.get_id_by_name(macro_name) {
            let attr_ty = ATTR_MAP.get(attr_id);
            let mut attr = Attr::new(macro_name, node.id());
            let mut is_valid = true;

            // We have to build the arguments to the macro invocation
            // in the form of an `Args` and then use TIR param_utils to
            // check that the arguments and parameters match...
            let (mac_args, args_node_id) = if let Some(mac_args) = node.args.as_ref() {
                let mut args = Vec::with_capacity(mac_args.args.len());

                for (index, arg) in mac_args.args.iter().enumerate() {
                    let target = if let Some(name) = arg.name.as_ref() {
                        ParamIndex::Name(name.ident)
                    } else {
                        ParamIndex::Position(index)
                    };

                    // If we can't convert this into an attribute value, then we
                    // can't properly check the invocation.
                    //
                    // @@Future: remove this restriction and allow more general
                    // expressions to be used as arguments to attributes.
                    let Some(attr_value) = AttrValueKind::try_from_expr(arg.value.body()) else {
                        let expr_kind = AttrTarget::classify_expr(arg.value.body());
                        self.diagnostics.add_error(ExpansionError::new(
                            ExpansionErrorKind::InvalidAttributeArg(expr_kind),
                            arg.id(),
                        ));

                        is_valid = false;
                        break;
                    };

                    macro_rules! lit_prim {
                        ($name:ident,$lit_name:ident, $contents:expr) => {
                            Term::from(Term::Lit(Lit::$name($lit_name::from($contents))))
                        };
                    }

                    let value = match attr_value {
                        AttrValueKind::Str(lit) => lit_prim!(Str, StrLit, lit),
                        AttrValueKind::Char(lit) => lit_prim!(Char, CharLit, lit),
                        AttrValueKind::Int(lit) => lit_prim!(Int, IntLit, lit),
                        AttrValueKind::Float(lit) => lit_prim!(Float, FloatLit, lit),
                    };

                    attr.add_arg(
                        AttrArgIdx::from(target),
                        AttrValue { origin: arg.id(), value: attr_value },
                    );
                    args.push(Arg { target, value });
                }

                (Arg::seq_data(args), mac_args.id())
            } else {
                (Arg::empty_seq(), node.name.id())
            };

            // Register the location of the args as the `mac_args` node.
            tir_stores().ast_info().args_seq().insert(args_node_id, mac_args);

            if is_valid && let Err(param_err) =
                self.param_utils().validate_and_reorder_args_against_params(mac_args, attr_ty.params)
            {
                self.diagnostics.add_error(ExpansionError::new(
                    ExpansionErrorKind::InvalidAttributeParams(param_err),
                    node.id,
                ));

                is_valid = false;
            }

            // Now we want to check that all of the types of the params and args match
            // up. @@Future: perhaps we could get TC do this for us, but for now we avoid
            // the dependency on TC.
            for (param_id, arg_id) in attr_ty.params.iter().zip(mac_args.iter()) {
                let arg_idx = arg_id.borrow().target.into();
                let param_ty = param_id.borrow().ty;

                is_valid &= self.check_attr_arg_and_param_tys_match(&attr, arg_idx, param_ty);
            }

            // Check that the subject of the attribute is correct...
            let target = subject.target();

            if !attr_ty.subject.contains(target) {
                self.diagnostics.add_error(ExpansionError::new(
                    ExpansionErrorKind::InvalidAttributeSubject { name: macro_name, target },
                    node.id(),
                ));

                is_valid = false;
            }

            // Finally, return the attribute if everything is ok!
            if is_valid {
                Some(attr)
            } else {
                None
            }
        } else {
            self.diagnostics.add_error(ExpansionError::new(
                ExpansionErrorKind::UnknownAttribute { name: macro_name },
                node.id,
            ));

            None
        }
    }

    /// Invoke a check on an attribute, and emit any diagnostics if the
    /// attribute is invalid.
    pub fn check_attrs(&mut self, attrs: &Attrs, attr: &Attr, subject: AttrNode<'_>) -> bool {
        let result = self.checker.check_attr(attrs, attr, subject);

        // Add any warnings that the checker may of produced.
        self.checker.take_warnings().into_iter().for_each(|warning| {
            self.diagnostics.add_warning(ExpansionWarning::new(warning.into(), attr.origin))
        });

        if let Err(error) = result {
            self.diagnostics.add_error(ExpansionError::new(
                ExpansionErrorKind::InvalidAttributeApplication(error),
                attr.origin,
            ));
            false
        } else {
            true
        }
    }
}
