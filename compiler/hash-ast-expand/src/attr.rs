//! Any logic related with attribute checking.

use hash_ast::ast;
use hash_ast_utils::{
    attr::{AttrNode, AttrTarget},
    dump::AstDump,
};
use hash_attrs::{
    attr::{Attr, AttrArgIdx, AttrValue, Attrs, attr_store},
    builtin::{ATTR_MAP, attrs},
};
use hash_repr::ty::COMMON_REPR_TYS;
use hash_storage::store::{
    TrivialSequenceStoreKey,
    statics::{SequenceStoreValue, StoreId},
};
use hash_target::HasTarget;
use hash_tir::{
    intrinsics::definitions::Primitive,
    tir::{
        Arg, Lit, Node, NodeOrigin, ParamIndex, Term, Ty, TyId,
        validate_and_reorder_args_against_params,
    },
};
use hash_utils::log;

use crate::{
    diagnostics::{
        error::{ExpansionError, ExpansionErrorKind},
        warning::ExpansionWarning,
    },
    expander::AstExpander,
};

impl AstExpander<'_> {
    pub fn check_macro_invocations(
        &mut self,
        node: ast::AstNodeRef<ast::MacroInvocations>,
        subject: AttrNode<'_>,
    ) {
        // If no attributes are present, return early...
        if node.invocations.is_empty() {
            return;
        }

        // Flag denoting whether we should invoke a `#dump_ast`
        // on the item.
        let mut should_dump = false;

        // If the macro invocation is correct, then we can append
        // all of the attributes that are being applied onto the
        // the target.
        let mut attrs = Attrs::with_capacity(node.body.invocations.len());
        let id = subject.id();

        for invocation in node.invocations.iter() {
            let maybe_attr = self.try_create_attr_from_macro(invocation.ast_ref(), subject);

            // Create a new attribute checker, and check that the attribute
            // is valid.
            if let Some(attr) = maybe_attr
                && self.check_attrs(&attrs, &attr, subject)
            {
                should_dump |= attr.id == attrs::DUMP_AST;
                attrs.add_attr(attr);
            }
        }

        attr_store().insert(id, attrs);

        if should_dump {
            let mode = self.settings.ast_settings.dump_mode;
            let character_set = self.settings.character_set;

            // @@Messaging: provide a format for the AST to be dumped in!
            log::info!("{}", AstDump::new(subject, mode, character_set));
        }
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
                self.add_error(ExpansionError::new(
                    ExpansionErrorKind::InvalidAttributeArgTy {
                        name: attr.id.name(),
                        target,
                        value,
                        ty: param_ty,
                    },
                    arg.origin,
                ));
            }

            matches
        };

        use Primitive::*;

        match *param_ty.value() {
            Ty::DataTy(data) => match Primitive::try_from_def(data.data_def) {
                Some(I8 | I16 | I32 | I64 | I128 | U8 | U16 | U32 | U64 | U128) => {
                    maybe_emit_err(value.ty().is_integral())
                }
                Some(F32 | F64) => maybe_emit_err(value.ty().is_float()),
                Some(Char) => maybe_emit_err(value.ty() == COMMON_REPR_TYS.char),
                Some(Str) => maybe_emit_err(value.ty() == COMMON_REPR_TYS.str),
                ty => panic!("unexpected attribute parameter type `{ty:?}`"),
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
            let mut attr = Attr::new(attr_id, node.id());
            let mut is_valid = true;

            // We have to build the arguments to the macro invocation
            // in the form of an `Args` and then use TIR param_utils to
            // check that the arguments and parameters match...
            let mac_args = if let Some(mac_args) = node.args.as_ref() {
                let mut args = Vec::with_capacity(mac_args.args.len());

                for (index, arg) in mac_args.args.iter().enumerate() {
                    let target = if let Some(name) = arg.name.as_ref() {
                        ParamIndex::Name(name.ident)
                    } else {
                        ParamIndex::pos(index)
                    };

                    let expected_ty = attr_ty.ty_of_param(target);
                    let ptr_size = self.settings.target().ptr_size();

                    // If we can't convert this into an attribute value, then we
                    // can't properly check the invocation.
                    let attr_value = match AttrValue::try_from_expr(
                        arg.id(),
                        arg.value.body(),
                        expected_ty,
                        ptr_size,
                    ) {
                        Ok(Some(value)) => value,
                        Ok(None) => {
                            let expr_kind = AttrTarget::classify_expr(arg.value.body());
                            self.add_error(ExpansionError::new(
                                ExpansionErrorKind::InvalidAttributeArg(expr_kind),
                                arg.id(),
                            ));

                            is_valid = false;
                            break;
                        }

                        // Literal parsing failed, we just push the error into the
                        // expansion diagnostics and let it be handled later.
                        Err(err) => {
                            self.add_error(ExpansionError::new(err.into(), node.id));

                            is_valid = false;
                            break;
                        }
                    };

                    attr.add_arg(AttrArgIdx::from(target), attr_value);

                    let value = Term::from(
                        Term::Lit(Node::create_at(
                            Lit::Const(attr_value.value),
                            NodeOrigin::Given(arg.value.id()),
                        )),
                        NodeOrigin::Given(arg.value.id()),
                    );
                    args.push(Node::at(Arg { target, value }, NodeOrigin::Given(arg.id())));
                }

                Node::create_at(Node::<Arg>::seq(args), NodeOrigin::Given(node.id()))
            } else {
                Node::create_at(Node::<Arg>::empty_seq(), NodeOrigin::Given(node.id()))
            };

            if is_valid
                && let Err(param_err) =
                    validate_and_reorder_args_against_params(mac_args, attr_ty.params)
            {
                self.add_error(ExpansionError::new(param_err.into(), node.id));

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
                self.add_error(ExpansionError::new(
                    ExpansionErrorKind::InvalidAttributeSubject { name: macro_name, target },
                    node.id(),
                ));

                is_valid = false;
            }

            // Finally, return the attribute if everything is ok!
            if is_valid { Some(attr) } else { None }
        } else {
            self.add_error(ExpansionError::new(
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
            self.add_warning(ExpansionWarning::new(warning.into(), attr.origin))
        });

        if let Err(error) = result {
            self.add_error(ExpansionError::new(
                ExpansionErrorKind::InvalidAttributeApplication(error),
                attr.origin,
            ));
            false
        } else {
            true
        }
    }
}
