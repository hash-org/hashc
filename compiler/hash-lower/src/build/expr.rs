//! Implementation for lowering [Expr]s into Hash IR. This module contains the
//! core logic of converting expressions into IR, other auxiliary conversion
//! `strategies` can be found in [crate::build::rvalue] and
//! [crate::build::temp].

use hash_ast::ast::{
    AccessExpr, AccessKind, AssignExpr, AssignOpExpr, AstNodeRef, AstNodes, BlockExpr,
    ConstructorCallArg, ConstructorCallExpr, Declaration, Expr, PropertyKind, RefExpr, RefKind,
    ReturnStatement, UnsafeExpr,
};
use hash_ir::{
    ir::{self, AddressMode, BasicBlock, Place, RValue, Statement, StatementKind, TerminatorKind},
    ty::{IrTy, Mutability, VariantIdx},
};
use hash_reporting::macros::panic_on_span;
use hash_source::location::Span;
use hash_utils::store::{SequenceStoreKey, Store};

use super::{unpack, BlockAnd, BlockAndExtend, Builder, LoopBlockInfo};

impl<'tcx> Builder<'tcx> {
    /// Compile the given [Expr] and place the value of the [Expr] into
    /// the specified destination [Place].
    pub(crate) fn expr_into_dest(
        &mut self,
        destination: Place,
        mut block: BasicBlock,
        expr: AstNodeRef<'tcx, Expr>,
    ) -> BlockAnd<()> {
        let span = expr.span();

        let block_and = match expr.body {
            Expr::ConstructorCall(ConstructorCallExpr { subject, args }) => {
                // Check the type of the subject, and if we need to
                // handle it as a constructor initialisation, or if it is a
                // function call.

                let subject_ty = self.ty_of_node(subject.id());

                if let IrTy::Fn { .. } = subject_ty {
                    self.fn_call_into_dest(destination, block, subject.ast_ref(), args, span)
                } else {
                    // This is a constructor call, so we need to handle it as such.
                    self.constructor_into_dest(destination, block, subject.ast_ref(), args)
                }
            }
            Expr::Directive(expr) => {
                self.expr_into_dest(destination, block, expr.subject.ast_ref())
            }
            Expr::Index(..)
            | Expr::Deref(..)
            | Expr::Access(AccessExpr { kind: AccessKind::Property, .. })
            | Expr::Variable(..) => {
                let _term = self.ty_of_node(expr.id());
                let place = unpack!(block = self.as_place(block, expr, Mutability::Immutable));

                let rvalue = self.storage.push_rvalue(RValue::Use(place));
                self.control_flow_graph.push_assign(block, destination, rvalue, span);

                block.unit()
            }
            Expr::Access(AccessExpr { subject, kind: AccessKind::Namespace, property }) => {
                // This is a special case, since we are creating an enum variant here with
                // no arguments.
                let subject_ty = self.ty_id_of_node(subject.id());
                let index = self.map_on_adt(subject_ty, |adt, _| match property.body() {
                    PropertyKind::NamedField(name) => adt.variant_idx(name).unwrap(),
                    PropertyKind::NumericField(index) => VariantIdx::from_usize(*index),
                });

                self.control_flow_graph.push(
                    block,
                    Statement { kind: StatementKind::Discriminate(destination, index), span },
                );

                block.unit()
            }
            Expr::Ref(RefExpr { inner_expr, kind, mutability }) => {
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
                    RefKind::Normal => AddressMode::Smart,
                    RefKind::Raw => AddressMode::Raw,
                };

                let place = unpack!(block = self.as_place(block, inner_expr.ast_ref(), mutability));

                // Create an RValue for this reference
                let addr_of = RValue::Ref(mutability, place, kind);
                let rvalue = self.storage.rvalue_store().create(addr_of);

                self.control_flow_graph.push_assign(block, destination, rvalue, span);
                block.unit()
            }
            Expr::Unsafe(UnsafeExpr { data }) => {
                self.expr_into_dest(destination, block, data.ast_ref())
            }

            // For declarations, we have to perform some bookkeeping in regards
            // to locals..., but this expression should never return any value
            // so we should just return a unit block here
            Expr::Declaration(decl) => self.handle_expr_declaration(block, decl),

            // Traverse the lhs of the cast, and then apply the cast
            // to the result... although this should be a no-op?
            Expr::Cast(..) => unimplemented!(),

            // This includes `loop { ... } `, `{ ... }`, `match { ... }`
            Expr::Block(BlockExpr { data }) => {
                self.block_into_dest(destination, block, data.ast_ref())
            }

            // We never do anything for these anyway...
            Expr::Import { .. }
            | Expr::StructDef { .. }
            | Expr::EnumDef { .. }
            | Expr::TyFnDef { .. }
            | Expr::TraitDef { .. }
            | Expr::ImplDef { .. }
            | Expr::ModDef { .. }
            | Expr::TraitImpl { .. }
            | Expr::MergeDeclaration { .. }
            | Expr::Ty { .. } => block.unit(),

            // @@Todo: we need be able to check here if this function is a closure,
            // and if so lower it as a closure. Similarly, any variables that are being
            // referenced from the environment above need special treatment when it comes
            // to a closure.
            Expr::FnDef(..) => block.unit(),

            Expr::Assign { .. } | Expr::AssignOp { .. } => {
                // Deal with the actual assignment
                block = unpack!(self.handle_statement_expr(block, expr));

                // Assign the `value` of the assignment into the `tmp_place`
                let const_value = ir::Const::zero(self.storage);

                let empty_value = self.storage.push_rvalue(RValue::Const(const_value));
                self.control_flow_graph.push_assign(block, destination, empty_value, span);
                block.unit()
            }

            Expr::Return(ReturnStatement { expr }) => {
                // In either case, we want to mark that the function has reached the
                // **terminating** statement of this block and we needn't continue looking
                // for more statements beyond this point.
                self.reached_terminator = true;

                // we want to set the return `place` with whatever the expression
                // is...
                if let Some(return_expr) = &expr {
                    unpack!(
                        block = self.expr_into_dest(
                            Place::return_place(),
                            block,
                            return_expr.ast_ref()
                        )
                    )
                } else {
                    // If no expression is attached to the return, then we need to push a
                    // `unit` value into the return place.
                    let const_value = ir::Const::zero(self.storage);

                    let unit = self.storage.push_rvalue(RValue::Const(const_value));
                    self.control_flow_graph.push_assign(block, Place::return_place(), unit, span);
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

            // These should be unreachable in this context
            Expr::Continue { .. } | Expr::Break { .. } => {
                // Specify that we have reached the terminator of this block...
                self.reached_terminator = true;

                // When this is a continue, we need to **jump** back to the
                // start of the loop block, and when this is a break, we need to
                // **jump** to the proceeding block of the loop block
                let Some(LoopBlockInfo { loop_body, next_block }) = self.loop_block_info else {
                    panic!("`continue` or `break` outside of loop");
                };

                // Add terminators to this block to specify where this block will jump...
                match expr.body {
                    Expr::Continue { .. } => {
                        self.control_flow_graph.goto(block, loop_body, span);
                    }
                    Expr::Break { .. } => {
                        self.control_flow_graph.goto(block, next_block, span);
                    }
                    _ => unreachable!(),
                }

                block.unit()
            }

            // Lower this as an Rvalue
            Expr::Lit(literal) => {
                let constant = self.as_constant(literal.data.ast_ref());
                let rvalue = self.storage.push_rvalue(constant.into());
                self.control_flow_graph.push_assign(block, destination, rvalue, span);

                block.unit()
            }

            Expr::BinaryExpr(..) | Expr::UnaryExpr(..) => {
                let rvalue = unpack!(block = self.as_rvalue(block, expr));
                self.control_flow_graph.push_assign(block, destination, rvalue, span);

                block.unit()
            }
        };

        block_and
    }

    /// This function handles the lowering of an expression declaration.
    /// Internally, we check if this declaration needs to be lowered since
    /// this might be declaring a free function within the current function
    /// body, and thus we should not lower it.
    ///
    /// @@Todo: deal with non-trivial dead-ends, i.e. compound patterns that
    /// have dead ends...
    pub(crate) fn handle_expr_declaration(
        &mut self,
        block: BasicBlock,
        decl: &'tcx Declaration,
    ) -> BlockAnd<()> {
        if self.dead_ends.contains(&decl.pat.id()) {
            return block.unit();
        }

        // Declare all locals that need to be declared based on the
        // pattern.
        self.visit_bindings(decl.pat.ast_ref());

        if let Some(rvalue) = &decl.value {
            self.expr_into_pat(block, decl.pat.ast_ref(), rvalue.ast_ref());
        } else {
            panic_on_span!(
                decl.pat.span().into_location(self.source_id),
                self.source_map,
                "expected initialisation value, declaration are expected to have values (for now)."
            );
        }

        // if the declaration has an initialiser, then we need to deal with
        // the initialisation block.
        block.unit()
    }

    pub(crate) fn handle_statement_expr(
        &mut self,
        mut block: BasicBlock,
        statement: AstNodeRef<'tcx, Expr>,
    ) -> BlockAnd<()> {
        match statement.body {
            Expr::Assign(AssignExpr { lhs, rhs }) => {
                let place =
                    unpack!(block = self.as_place(block, lhs.ast_ref(), Mutability::Mutable));
                let value = unpack!(block = self.as_rvalue(block, rhs.ast_ref()));
                self.control_flow_graph.push_assign(block, place, value, statement.span());

                block.unit()
            }
            Expr::AssignOp(AssignOpExpr { lhs: _, rhs: _, operator: _ }) => {
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
        subject: AstNodeRef<'tcx, Expr>,
        args: &'tcx AstNodes<ConstructorCallArg>,
        span: Span,
    ) -> BlockAnd<()> {
        // First we want to lower the subject of the function call
        let func = unpack!(block = self.as_rvalue(block, subject));

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
        let fn_ty = self.ty_of_node(subject.id());

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
                unpack!(block = self.as_rvalue(block, value))
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

    pub fn constructor_into_dest(
        &mut self,
        _destination: Place,
        mut _block: BasicBlock,
        _subject: AstNodeRef<'tcx, Expr>,
        _args: &'tcx AstNodes<ConstructorCallArg>,
    ) -> BlockAnd<()> {
        unimplemented!()
    }
}
