//! Utilities for dealing with [Place]s when building up Hash IR.
#![allow(unused)]

use hash_ast::ast::{AstNodeRef, Expr};
use hash_ir::{
    ir::{BasicBlock, Local, Place, PlaceProjection},
    ty::Mutability,
};

use super::{unpack, BlockAnd, BlockAndExtend, Builder};

/// A builder interface for building a [Place] with a base [Local]
/// and a collection of projections that are applied as the
/// [Place] is constructed.
pub struct PlaceBuilder {
    /// The place that we are building.
    base: Local,

    /// All of the current projections that are being applied on the [Local].
    projections: Vec<PlaceProjection>,
}

impl PlaceBuilder {
    pub(crate) fn new(base: Local) -> Self {
        Self { base, projections: Vec::new() }
    }

    /// Apply a [PlaceProjection::Deref] to the [PlaceBuilder].
    pub(crate) fn deref(self) -> Self {
        self.project(PlaceProjection::Deref)
    }

    /// Apply a [PlaceProjection::Field] to the [PlaceBuilder].
    pub(crate) fn field(self, index: usize) -> Self {
        self.project(PlaceProjection::Field(index))
    }

    /// Apply a [PlaceProjection::Index] to the [PlaceBuilder].
    pub(crate) fn index(self, index: Local) -> Self {
        self.project(PlaceProjection::Index(index))
    }

    /// Apply a [PlaceProjection::Downcast] to the [PlaceBuilder].
    pub(crate) fn downcast(self, index: usize) -> Self {
        self.project(PlaceProjection::Downcast(index))
    }

    /// Apply a [PlaceProjection] onto the current [PlaceBuilder].
    pub(crate) fn project(mut self, projection: PlaceProjection) -> Self {
        self.projections.push(projection);
        self
    }

    /// Build the [Place] from the [PlaceBuilder].
    pub(crate) fn into_place(self) -> Place {
        Place { local: self.base, projections: self.projections }
    }
}

impl From<Local> for PlaceBuilder {
    fn from(value: Local) -> Self {
        Self::new(value)
    }
}

impl<'tcx> Builder<'tcx> {
    pub(crate) fn as_place(
        &mut self,
        mut block: BasicBlock,
        expr: AstNodeRef<'tcx, Expr>,
        mutability: Mutability,
    ) -> BlockAnd<Place> {
        let place_builder = unpack!(block = self.as_place_builder(block, expr, mutability));
        block.and(place_builder.into_place())
    }

    pub(crate) fn as_place_builder(
        &mut self,
        mut block: BasicBlock,
        expr: AstNodeRef<'tcx, Expr>,
        mutability: Mutability,
    ) -> BlockAnd<PlaceBuilder> {
        match expr.body {
            Expr::Variable(variable) => {
                // Get the current scope, and resolve the variable within the scope. This will
                // get us the scope that this variable comes from. Using the id and the name, we
                // can then lookup the local that this variable is bound to.
                let name = variable.name.ident;

                let local = self.lookup_local(name).unwrap();
                block.and(PlaceBuilder::from(local))
            }
            Expr::Ref(_) => todo!(),
            Expr::Access(_) => todo!(),
            Expr::Deref(_) => todo!(),
            Expr::Index(_) => todo!(),

            Expr::Import(_)
            | Expr::StructDef(_)
            | Expr::EnumDef(_)
            | Expr::TyFnDef(_)
            | Expr::TraitDef(_)
            | Expr::FnDef(_)
            | Expr::MergeDeclaration(_)
            | Expr::TraitImpl(_)
            | Expr::Directive(_) => {
                // We should never encounter these expressions when we are building
                // a place, this means that someone passed an expression that shouldn't
                // be put into a place.
                unreachable!()
            }

            Expr::ConstructorCall(_)
            | Expr::Declaration(_)
            | Expr::Unsafe(_)
            | Expr::Lit(_)
            | Expr::Cast(_)
            | Expr::Block(_)
            | Expr::Ty(_)
            | Expr::Return(_)
            | Expr::Break(_)
            | Expr::Continue(_)
            | Expr::Assign(_)
            | Expr::AssignOp(_)
            | Expr::BinaryExpr(_)
            | Expr::UnaryExpr(_) => {
                // These expressions are not places, so we need to create a temporary
                // and then deal with it.
                let temp = unpack!(block = self.expr_into_temp(block, expr, mutability));
                block.and(PlaceBuilder::from(temp))
            }
        }
    }
}
