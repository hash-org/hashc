//! Any logic related with attribute checking.

use hash_ast::ast;
use hash_ast_utils::{
    attr::{AttrNode, AttrTarget},
    dump::dump_ast,
};
use hash_attrs::{
    attr::{attr_store, Attr, AttrArgIdx, AttrValue, AttrValueKind, Attrs},
    builtin::{attrs, ATTR_MAP},
};
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    TrivialSequenceStoreKey,
};
use hash_target::HasTarget;
use hash_tir::{
    args::Arg,
    lits::{CharLit, FloatLit, IntLit, Lit, StrLit},
    node::{Node, NodeOrigin},
    params::ParamIndex,
    primitives::primitives,
    terms::{Term, Ty, TyId},
    utils::params::ParamUtils,
};

use crate::{
    diagnostics::{
        error::{ExpansionError, ExpansionErrorKind},
        warning::ExpansionWarning,
    },
    expander::AstExpander,
};

impl AstExpander<'_> {
    /// Make a [ParamUtils].
    fn param_utils(&self) -> ParamUtils {
        ParamUtils
    }

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
            if let Some(attr) = maybe_attr && self.check_attrs(&attrs, &attr, subject) {
                should_dump |= attr.id == attrs::DUMP_AST;
                attrs.add_attr(attr);
            }
        }

        attr_store().insert(id, attrs);

        if should_dump {
            let mode = self.settings.ast_settings.dump_mode;
            let character_set = self.settings.character_set;
            dump_ast(subject, mode, character_set, &mut self.stdout).unwrap();
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

        match *param_ty.value() {
            Ty::DataTy(data) => match data.data_def {
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
                        ParamIndex::Position(index)
                    };

                    let ptr_size = self.settings.target().ptr_size();

                    // If we can't convert this into an attribute value, then we
                    // can't properly check the invocation.
                    let attr_value = match AttrValueKind::try_from_expr(arg.value.body(), ptr_size)
                    {
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

                    macro_rules! lit_prim {
                        ($name:ident,$lit_name:ident, $contents:expr) => {
                            Term::from(
                                Term::Lit(Node::create_at(
                                    Lit::$name($lit_name::from($contents)),
                                    NodeOrigin::Given(arg.value.id()),
                                )),
                                NodeOrigin::Given(arg.value.id()),
                            )
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
                    args.push(Node::at(Arg { target, value }, NodeOrigin::Given(arg.id())));
                }

                Node::create_at(Node::<Arg>::seq(args), NodeOrigin::Given(node.id()))
            } else {
                Node::create_at(Node::<Arg>::empty_seq(), NodeOrigin::Given(node.id()))
            };

            if is_valid && let Err(param_err) =
                self.param_utils().validate_and_reorder_args_against_params(mac_args, attr_ty.params)
            {
                self.add_error(ExpansionError::new(
                    param_err.into(),
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
                self.add_error(ExpansionError::new(
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
