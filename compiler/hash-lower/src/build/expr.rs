//! Implementation for lowering [ast::Expr]s into Hash IR. This module contains
//! the core logic of converting expressions into IR, other auxiliary conversion
//! `strategies` can be found in [crate::build::rvalue] and
//! [crate::build::temp].

use hash_ast::ast;
use hash_ir::{
    ir::{
        self, AggregateKind, BasicBlock, Const, ConstKind, Place, RValue, Statement, StatementKind,
        TerminatorKind, UnevaluatedConst,
    },
    ty::{AdtId, IrTy, Mutability, RefKind, VariantIdx},
};
use hash_reporting::macros::panic_on_span;
use hash_source::{identifier::Identifier, location::Span};
use hash_tir::scope::ScopeKind;
use hash_utils::store::{SequenceStoreKey, Store};

use super::{unpack, BlockAnd, BlockAndExtend, Builder, LoopBlockInfo};

impl<'tcx> Builder<'tcx> {
    /// Compile the given [ast::Expr] and place the value of the [ast::Expr]
    /// into the specified destination [Place].
    pub(crate) fn expr_into_dest(
        &mut self,
        destination: Place,
        mut block: BasicBlock,
        expr: ast::AstNodeRef<'tcx, ast::Expr>,
    ) -> BlockAnd<()> {
        let span = expr.span();

        let block_and = match expr.body {
            ast::Expr::ConstructorCall(ast::ConstructorCallExpr { subject, args }) => {
                // Check the type of the subject, and if we need to
                // handle it as a constructor initialisation, or if it is a
                // function call.
                let subject_ty = self.ty_of_node(subject.id());

                if let IrTy::Fn { .. } = subject_ty {
                    self.fn_call_into_dest(
                        destination,
                        block,
                        subject.ast_ref(),
                        subject_ty,
                        args,
                        span,
                    )
                } else if let IrTy::Adt(adt) = subject_ty {
                    // This is a constructor call, so we need to handle it as such.
                    self.constructor_into_dest(
                        destination,
                        block,
                        subject.ast_ref(),
                        adt,
                        args,
                        span,
                    )
                } else {
                    // A constructor cannot be typed anything but either a function or some
                    // ADT.
                    unreachable!()
                }
            }
            ast::Expr::Directive(expr) => {
                self.expr_into_dest(destination, block, expr.subject.ast_ref())
            }
            ast::Expr::Index(..)
            | ast::Expr::Deref(..)
            | ast::Expr::Access(ast::AccessExpr { kind: ast::AccessKind::Property, .. }) => {
                let place = unpack!(block = self.as_place(block, expr, Mutability::Immutable));
                self.control_flow_graph.push_assign(block, destination, place.into(), span);

                block.unit()
            }
            ast::Expr::Variable(ast::VariableExpr { name }) => {
                let name = name.ident;
                let (scope, _, scope_kind) = self.lookup_item_scope(name).unwrap();

                // Here, if the scope is not variable, i.e. constant, then we essentially need
                // to denote that this a constant that comes from outside of the function body.
                if !matches!(scope_kind, ScopeKind::Variable) {
                    // here, we emit an un-evaluated constant kind which will be resolved later
                    // during IR simplification.
                    let unevaluated_const = UnevaluatedConst { scope, name };
                    let rvalue = (ConstKind::Unevaluated(unevaluated_const)).into();

                    // we also need to save this un-evaluated const in the builder
                    // so we can easily know what should and shouldn't be resolved.
                    self.needed_constants.push(unevaluated_const);
                    self.control_flow_graph.push_assign(block, destination, rvalue, span);
                } else {
                    let local = self.lookup_local_from_scope(scope, name).unwrap();
                    let place = Place::from_local(local, self.ctx);
                    self.control_flow_graph.push_assign(block, destination, place.into(), span);
                }

                block.unit()
            }
            ast::Expr::Access(ast::AccessExpr {
                subject,
                kind: ast::AccessKind::Namespace,
                property,
            }) => {
                // This is a special case, since we are creating an enum variant here with
                // no arguments.
                let subject_ty = self.ty_id_of_node(subject.id());
                let index = self.ctx.map_ty_as_adt(subject_ty, |adt, _| match property.body() {
                    ast::PropertyKind::NamedField(name) => adt.variant_idx(name).unwrap(),
                    ast::PropertyKind::NumericField(index) => VariantIdx::from_usize(*index),
                });

                self.control_flow_graph.push(
                    block,
                    Statement { kind: StatementKind::Discriminate(destination, index), span },
                );

                block.unit()
            }
            ast::Expr::Ref(ast::RefExpr { inner_expr, kind, mutability }) => {
                let mutability = if let Some(specified_mut) = mutability {
                    (*specified_mut.body()).into()
                } else {
                    Mutability::Immutable
                };

                // @@Todo: This is not the full picture here, if the user only specifies a
                // `Normal` ref, this still might become a `SmartRef` based on
                // the type of the expression, and where the expression comes
                // from.
                let kind = match kind {
                    ast::RefKind::Normal => RefKind::Normal,
                    ast::RefKind::Raw => RefKind::Raw,
                };

                let place = unpack!(block = self.as_place(block, inner_expr.ast_ref(), mutability));

                // Create an RValue for this reference
                let addr_of = RValue::Ref(mutability, place, kind);
                self.control_flow_graph.push_assign(block, destination, addr_of, span);
                block.unit()
            }
            ast::Expr::Unsafe(ast::UnsafeExpr { data }) => {
                self.expr_into_dest(destination, block, data.ast_ref())
            }

            // For declarations, we have to perform some bookkeeping in regards
            // to locals..., but this expression should never return any value
            // so we should just return a unit block here
            ast::Expr::Declaration(decl) => self.lower_declaration(block, decl, span),

            // Traverse the lhs of the cast, and then apply the cast
            // to the result... although this should be a no-op?
            ast::Expr::Cast(..) => unimplemented!(),

            // This includes `loop { ... } `, `{ ... }`, `match { ... }`
            ast::Expr::Block(ast::BlockExpr { data }) => {
                self.block_into_dest(destination, block, data.ast_ref())
            }

            // We never do anything for these anyway...
            ast::Expr::Import { .. }
            | ast::Expr::StructDef { .. }
            | ast::Expr::EnumDef { .. }
            | ast::Expr::TyFnDef { .. }
            | ast::Expr::TraitDef { .. }
            | ast::Expr::ImplDef { .. }
            | ast::Expr::ModDef { .. }
            | ast::Expr::TraitImpl { .. }
            | ast::Expr::MergeDeclaration { .. }
            | ast::Expr::Ty { .. } => block.unit(),

            // @@Todo: we need be able to check here if this function is a closure,
            // and if so lower it as a closure. Similarly, any variables that are being
            // referenced from the environment above need special treatment when it comes
            // to a closure.
            ast::Expr::FnDef(..) => block.unit(),

            ast::Expr::Assign { .. } | ast::Expr::AssignOp { .. } => {
                // Deal with the actual assignment
                block = unpack!(self.handle_statement_expr(block, expr));

                // Assign the `value` of the assignment into the `tmp_place`
                let const_value = ir::Const::zero(self.ctx);
                self.control_flow_graph.push_assign(block, destination, const_value.into(), span);

                block.unit()
            }

            ast::Expr::Return(ast::ReturnStatement { expr }) => {
                // In either case, we want to mark that the function has reached the
                // **terminating** statement of this block and we needn't continue looking
                // for more statements beyond this point.
                self.reached_terminator = true;

                // we want to set the return `place` with whatever the expression
                // is...
                if let Some(return_expr) = &expr {
                    unpack!(
                        block = self.expr_into_dest(
                            Place::return_place(self.ctx),
                            block,
                            return_expr.ast_ref()
                        )
                    )
                } else {
                    // If no expression is attached to the return, then we need to push a
                    // `unit` value into the return place.
                    let const_value = ir::Const::zero(self.ctx);

                    self.control_flow_graph.push_assign(
                        block,
                        Place::return_place(self.ctx),
                        const_value.into(),
                        span,
                    );
                }

                // Create a new block for the `return` statement and make this block
                // go to the return whilst also starting a new block.
                //
                // @@Note: during CFG simplification, this edge will be removed and unified with
                // the `exit` block.
                let return_block = self.control_flow_graph.make_return_block();
                self.control_flow_graph.goto(block, return_block, span);
                self.control_flow_graph.start_new_block().unit()
            }

            ast::Expr::Continue { .. } | ast::Expr::Break { .. } => {
                // Specify that we have reached the terminator of this block...
                self.reached_terminator = true;

                // When this is a continue, we need to **jump** back to the
                // start of the loop block, and when this is a break, we need to
                // **jump** to the proceeding block of the loop block
                let Some(LoopBlockInfo { loop_body, next_block }) = self.loop_block_info else {
                    panic_on_span!(
                        span.into_location(self.source_id),
                        self.source_map,
                        "`continue` or `break` outside of loop"
                    );
                };

                // Add terminators to this block to specify where this block will jump...
                match expr.body {
                    ast::Expr::Continue { .. } => {
                        self.control_flow_graph.goto(block, loop_body, span);
                    }
                    ast::Expr::Break { .. } => {
                        self.control_flow_graph.goto(block, next_block, span);
                    }
                    _ => unreachable!(),
                }

                block.unit()
            }

            ast::Expr::Lit(literal) => {
                // We lower primitive (integrals, strings, etc) literals as constants, and
                // other literals like `sets`, `maps`, `lists`, and `tuples` as aggregates.
                match literal.data.body() {
                    ast::Lit::Map(_) | ast::Lit::Set(_) => unimplemented!(),
                    ast::Lit::List(ast::ListLit { elements }) => {
                        let ty = self.ty_id_of_node(expr.id());
                        let el_ty = self.ctx.map_ty(ty, |ty| match ty {
                            IrTy::Slice(ty) | IrTy::Array { ty, .. } => *ty,
                            _ => unreachable!(),
                        });

                        let aggregate_kind = AggregateKind::Array(el_ty);
                        let args = elements
                            .iter()
                            .enumerate()
                            .map(|(index, element)| (index.into(), element.ast_ref()))
                            .collect::<Vec<_>>();

                        self.aggregate_into_dest(destination, block, aggregate_kind, &args, span)
                    }
                    ast::Lit::Tuple(ast::TupleLit { elements }) => {
                        let ty = self.ty_id_of_node(expr.id());
                        let adt = self.ctx.map_ty_as_adt(ty, |_, id| id);
                        let aggregate_kind = AggregateKind::Tuple(adt);

                        let args = elements
                            .iter()
                            .enumerate()
                            .map(|(index, element)| {
                                let name = match &element.body().name {
                                    Some(name) => name.ident,
                                    None => index.into(),
                                };

                                (name, element.body().value.ast_ref())
                            })
                            .collect::<Vec<_>>();

                        self.aggregate_into_dest(destination, block, aggregate_kind, &args, span)
                    }
                    ast::Lit::Str(_)
                    | ast::Lit::Char(_)
                    | ast::Lit::Int(_)
                    | ast::Lit::Float(_)
                    | ast::Lit::Bool(_) => {
                        let constant = self.as_constant(literal.data.ast_ref());
                        self.control_flow_graph.push_assign(
                            block,
                            destination,
                            constant.into(),
                            span,
                        );

                        block.unit()
                    }
                }
            }

            // We deal with logical binary expressions differently than other
            // binary operators. In order to preserve the short-circuiting behaviour of
            // these operators, we need to create the following schemes:
            //
            // AND operator:
            // ```text
            //  +-----+  true   +------------+
            //  | lhs |-------->| dest = rhs |--+
            //  +--+--+         +------------+  |
            //     |                            |
            //     | false                      |
            //     v                            |
            //  +--+-----------+                |   +------+
            //  | dest = false |----------------+-->| join |
            //  +--------------+                    +------+
            // ```
            //
            // OR operator:
            //
            // ```text
            //  +-----+  false  +------------+
            //  | lhs |-------->| dest = rhs |--+
            //  +--+--+         +------------+  |
            //     |                            |
            //     | true                       |
            //     v                            |
            //  +--+-----------+                |   +------+
            //  | dest = true  |----------------+-->| join |
            //  +--------------+                    +------+
            // ```
            ast::Expr::BinaryExpr(ast::BinaryExpr { lhs, rhs, operator }) if operator.is_lazy() => {
                let (short_circuiting_block, mut else_block, join_block) = (
                    self.control_flow_graph.start_new_block(),
                    self.control_flow_graph.start_new_block(),
                    self.control_flow_graph.start_new_block(),
                );

                let lhs =
                    unpack!(block = self.as_operand(block, lhs.ast_ref(), Mutability::Mutable));

                let blocks = match *operator.body() {
                    ast::BinOp::And => (else_block, short_circuiting_block),
                    ast::BinOp::Or => (short_circuiting_block, else_block),
                    _ => unreachable!(),
                };

                let term = TerminatorKind::make_if(lhs, blocks.0, blocks.1, self.ctx);
                self.control_flow_graph.terminate(block, span, term);

                // Create the constant that we will assign in the `short_circuiting` block.
                let constant = match *operator.body() {
                    ast::BinOp::And => Const::Bool(false),
                    ast::BinOp::Or => Const::Bool(true),
                    _ => unreachable!(),
                };

                self.control_flow_graph.push_assign(
                    short_circuiting_block,
                    destination,
                    constant.into(),
                    span,
                );

                // Join the branch to the joining block
                self.control_flow_graph.goto(short_circuiting_block, join_block, span);

                // Now deal with the non-short-circuiting block
                let rhs = unpack!(
                    else_block = self.as_operand(else_block, rhs.ast_ref(), Mutability::Mutable)
                );

                self.control_flow_graph.push_assign(else_block, destination, rhs.into(), span);
                self.control_flow_graph.goto(else_block, join_block, span);

                join_block.unit()
            }

            ast::Expr::BinaryExpr(..) | ast::Expr::UnaryExpr(..) => {
                let rvalue = unpack!(block = self.as_rvalue(block, expr));
                self.control_flow_graph.push_assign(block, destination, rvalue, span);

                block.unit()
            }
        };

        block_and
    }

    pub(crate) fn handle_statement_expr(
        &mut self,
        mut block: BasicBlock,
        statement: ast::AstNodeRef<'tcx, ast::Expr>,
    ) -> BlockAnd<()> {
        match statement.body {
            ast::Expr::Assign(ast::AssignExpr { lhs, rhs }) => {
                let place =
                    unpack!(block = self.as_place(block, lhs.ast_ref(), Mutability::Mutable));
                let value = unpack!(block = self.as_rvalue(block, rhs.ast_ref()));
                self.control_flow_graph.push_assign(block, place, value, statement.span());

                block.unit()
            }
            ast::Expr::AssignOp(ast::AssignOpExpr { lhs: _, rhs: _, operator: _ }) => {
                // @@Todo: implement this when operators work properly
                block.unit()
            }

            _ => unreachable!(),
        }
    }

    /// Lower a function call and place the result into the provided
    /// destination.
    pub fn fn_call_into_dest(
        &mut self,
        destination: Place,
        mut block: BasicBlock,
        subject: ast::AstNodeRef<'tcx, ast::Expr>,
        fn_ty: IrTy,
        args: &'tcx ast::AstNodes<ast::ConstructorCallArg>,
        span: Span,
    ) -> BlockAnd<()> {
        // First we want to lower the subject of the function call
        let func = unpack!(block = self.as_operand(block, subject, Mutability::Immutable));

        // lower the arguments of the function...
        //
        // @@Todo: we need to deal with default arguments here, we compute the missing
        // arguments, and then insert a lowered copy of the default value for
        // the argument.
        //
        // @@Future: this means we would have to have a way of referencing
        // the default value of an argument, which is not currently possible in
        // the AST. One way could be to build a map when traversing the AST that
        // can map between the argument and the default value, later being fetched
        // when we need to **fill** in the missing argument.
        if let IrTy::Fn { params, .. } = fn_ty {
            if args.len() != params.len() {
                panic_on_span!(
                    span.into_location(self.source_id),
                    self.source_map,
                    "default arguments on functions are not currently supported",
                );
            }
        }

        let args = args
            .iter()
            .map(|arg| {
                let value = arg.value.ast_ref();
                unpack!(block = self.as_operand(block, value, Mutability::Immutable))
            })
            .collect::<Vec<_>>();

        // This is the block that is used when resuming from the function..
        let success = self.control_flow_graph.start_new_block();

        // Terminate the current block with a `Call` terminator
        self.control_flow_graph.terminate(
            block,
            span,
            TerminatorKind::Call { op: func, args, destination, target: Some(success) },
        );

        success.unit()
    }

    /// Function that deals with lowering a constructor call which might involve
    /// either a `struct` or an `enum` constructor. This function constructs an
    /// [RValue::Aggregate] and assigns it to the specified destination.
    ///
    /// However, due to the fact that we haven't decided whether it is easier to
    /// deal with aggregate values or direct fields assignments, we might have
    /// to end up de-aggregating the aggregate values into a series of
    /// assignments as they are specified within their declaration order.
    pub fn constructor_into_dest(
        &mut self,
        destination: Place,
        mut block: BasicBlock,
        subject: ast::AstNodeRef<'tcx, ast::Expr>,
        adt_id: AdtId,
        args: &'tcx ast::AstNodes<ast::ConstructorCallArg>,
        span: Span,
    ) -> BlockAnd<()> {
        let aggregate_kind = self.ctx.adts().map_fast(adt_id, |adt| {
            if adt.flags.is_enum() || adt.flags.is_union() {
                // here, we have to work out which variant is being used, so we look at the
                // subject type as an `enum variant` value, and extract the index
                let index = if let ast::Expr::Access(ast::AccessExpr {
                    property,
                    kind: ast::AccessKind::Namespace,
                    ..
                }) = &subject.body
                {
                    match property.body() {
                        ast::PropertyKind::NamedField(name) => adt.variant_idx(name).unwrap(),
                        ast::PropertyKind::NumericField(index) => VariantIdx::from_usize(*index),
                    }
                } else {
                    panic!("expected an enum variant")
                };

                AggregateKind::Enum(adt_id, index)
            } else {
                debug_assert!(adt.flags.is_struct());
                AggregateKind::Struct(adt_id)
            }
        });

        // deal with the subject first, since it might involve creating a
        // discriminant on the destination.
        if matches!(aggregate_kind, AggregateKind::Enum(..)) {
            unpack!(block = self.expr_into_dest(destination, block, subject));
        }

        let args = args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                let name = match &arg.name {
                    Some(name) => name.ident,
                    None => index.into(),
                };

                (name, arg.value.ast_ref())
            })
            .collect::<Vec<_>>();

        self.aggregate_into_dest(destination, block, aggregate_kind, &args, span)
    }

    /// Place any aggregate value into the specified destination. This does not
    /// currently deal with default arguments to a specified ADT, so it will
    /// panic if the number of arguments provided is not equal to the number of
    /// fields in the ADT.
    fn aggregate_into_dest(
        &mut self,
        destination: Place,
        mut block: BasicBlock,
        aggregate_kind: AggregateKind,
        args: &[(Identifier, ast::AstNodeRef<'tcx, ast::Expr>)],
        span: Span,
    ) -> BlockAnd<()> {
        // We don't need to perform this check for arrays since they don't need
        // to have a specific amount of arguments to the constructor.
        let fields: Vec<_> = if aggregate_kind.is_adt() {
            let adt_id = aggregate_kind.adt_id();

            // We have to evaluate each field in the specified source
            // order despite the aggregate potentially having a different
            // field order.
            let mut field_map = Vec::with_capacity(args.len());
            let mut field_names = Vec::with_capacity(args.len());

            // @@Todo: deal with the situation where we need to fill in default
            //  values for various parameters. For now, we ensure that all
            //  values are specified for the particular definition, and ensure
            // that the provided fields are equal. When we do add support for
            // default field values, it should be that the type checker
            // emits information about what fields need to be added to this
            // aggregate value.
            for (name, field) in args {
                let value = unpack!(block = self.as_operand(block, *field, Mutability::Immutable));
                field_map.push(value);
                field_names.push(*name);
            }

            self.ctx.adts().map_fast(adt_id, |adt| {
                let variant = if let AggregateKind::Enum(_, index) = aggregate_kind {
                    &adt.variants[index]
                } else {
                    &adt.variants[0]
                };

                let field_count = variant.fields.len();

                // Ensure we have the exact amount of arguments as the definition expects.
                if args.len() != field_count {
                    panic_on_span!(
                        span.into_location(self.source_id),
                        self.source_map,
                        "default arguments on constructors are not currently supported",
                    );
                }

                // now we re-order the field_map in the "expected" order
                // of the aggregate initialisation...
                for (index, name) in field_names.iter().enumerate() {
                    let field_index = variant.field_idx(*name).unwrap();

                    if field_index == index {
                        continue;
                    }

                    field_map.swap(index, field_index);
                }

                field_map
            })
        } else {
            // This aggregate kind is an array, so all that we do is just
            // lower each of the arguments into the array.
            args.iter()
                .map(|(_, arg)| {
                    unpack!(block = self.as_operand(block, *arg, Mutability::Immutable))
                })
                .collect()
        };

        let aggregate = RValue::Aggregate(aggregate_kind, fields);
        self.control_flow_graph.push_assign(block, destination, aggregate, span);

        block.unit()
    }
}
