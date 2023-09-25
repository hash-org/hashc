//! Utilities for dealing with [Place]s when building up Hash IR.

use hash_ir::{
    ir::{BasicBlock, Local, Place, PlaceProjection, ProjectionId},
    ty::{IrTyId, Mutability, VariantIdx},
};
use hash_storage::store::statics::StoreId;
use hash_tir::tir::{AccessTerm, DerefTerm, IndexTerm, ParamIndex, Term, TermId, Ty};

use super::{unpack, BlockAnd, BlockAndExtend, BodyBuilder};

/// A builder interface for building a [Place] with a base [Local]
/// and a collection of projections that are applied as the
/// [Place] is constructed.
#[derive(Debug, Clone, PartialEq)]
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
    pub(crate) fn downcast(self, index: VariantIdx) -> Self {
        self.project(PlaceProjection::Downcast(index))
    }

    /// Apply a [PlaceProjection] onto the current [PlaceBuilder].
    pub(crate) fn project(mut self, projection: PlaceProjection) -> Self {
        self.projections.push(projection);
        self
    }

    /// Clone the [PlaceBuilder], and then apply a [PlaceProjection]. This
    /// is more efficient that calling `place.clone().project()`.
    pub(crate) fn clone_project(&self, projection: PlaceProjection) -> Self {
        Self {
            base: self.base,
            projections: Vec::from_iter(
                self.projections.iter().copied().chain(std::iter::once(projection)),
            ),
        }
    }

    /// Build the [Place] from the [PlaceBuilder].
    pub(crate) fn into_place(self) -> Place {
        Place { local: self.base, projections: ProjectionId::seq(self.projections) }
    }
}

impl From<Local> for PlaceBuilder {
    fn from(value: Local) -> Self {
        Self::new(value)
    }
}

impl<'tcx> BodyBuilder<'tcx> {
    pub(crate) fn as_place(
        &mut self,
        mut block: BasicBlock,
        term: TermId,
        mutability: Mutability,
    ) -> BlockAnd<Place> {
        let place_builder = unpack!(block = self.as_place_builder(block, term, mutability));
        block.and(place_builder.into_place())
    }

    pub(crate) fn as_place_builder(
        &mut self,
        mut block: BasicBlock,
        term: TermId,
        mutability: Mutability,
    ) -> BlockAnd<PlaceBuilder> {
        match *term.value() {
            Term::Var(var) => {
                // Get the current scope, and resolve the variable within the scope. This will
                // get us the scope that this variable comes from. Using the id and the name, we
                // can then lookup the local that this variable is bound to.
                let local = self
                    .lookup_local(var.symbol)
                    .unwrap_or_else(|| panic!("failed to lookup local `{}`", var.symbol.ident()));
                block.and(PlaceBuilder::from(local))
            }
            Term::Access(AccessTerm { subject, field }) => {
                let place_builder =
                    unpack!(block = self.as_place_builder(block, subject, mutability));

                let subject_ty = self.ty_id_from_tir_term(subject);

                let index = self.lookup_field_index(subject_ty, field);
                block.and(place_builder.field(index))
            }
            Term::Deref(DerefTerm { subject }) => {
                let place_builder =
                    unpack!(block = self.as_place_builder(block, subject, mutability));
                block.and(place_builder.deref())
            }
            Term::Index(IndexTerm { subject, index }) => {
                let mut base_place =
                    unpack!(block = self.as_place_builder(block, subject, mutability));

                // Create a temporary for the index expression.
                let index = unpack!(block = self.term_into_temp(block, index, mutability));

                // Auto-deref: if the base place is behind a reference, then we dereference
                // it.
                let ty = self.ty_id_from_tir_term(subject);

                if ty.borrow().is_ref() {
                    base_place = base_place.deref()
                }

                // @@Todo: depending on the configuration, we may need to insert a bounds check
                // here.
                block.and(base_place.index(index))
            }
            Term::Tuple(_)
            | Term::Lit(_)
            | Term::Array(_)
            | Term::Call(_)
            | Term::Ctor(_)
            | Term::Fn(_)
            | Term::Intrinsic(_)
            | Term::Block(_)
            | Term::Loop(_)
            | Term::LoopControl(_)
            | Term::Match(_)
            | Term::Return(_)
            | Term::Assign(_)
            | Term::Unsafe(_)
            | Term::Cast(_)
            | Term::TypeOf(_)
            | Ty::DataTy(_)
            | Ty::FnTy(_)
            | Ty::TupleTy(_)
            | Ty::RefTy(_)
            | Ty::Universe
            | Term::Ref(_)
            | Term::Hole(_) => {
                // These expressions are not places, so we need to create a temporary
                // and then deal with it.
                let temp = unpack!(block = self.term_into_temp(block, term, mutability));
                block.and(PlaceBuilder::from(temp))
            }
        }
    }

    /// Function to lookup the index of a particular field within a [IrTyId]
    /// using a [ParamIndex]. This function assumes that the underlying type
    /// is a [IrTy::Adt].
    fn lookup_field_index(&mut self, ty: IrTyId, field: ParamIndex) -> usize {
        ty.borrow().as_adt().map(|adt| {
            // @@Todo: deal with unions here.
            if adt.flags.is_struct() || adt.flags.is_tuple() {
                // So we get the first variant of the ADT since structs, tuples always
                // have a single variant
                let variant = adt.variants.first().unwrap();

                match field {
                    ParamIndex::Name(name) => {
                        // @@Optimisation: we could use a lookup table for `AdtField` to
                        // immediately lookup the field rather than looping through the
                        // whole vector trying to find the field with the same name.
                        variant.fields.iter().position(|field| field.name == name).unwrap()
                    }
                    ParamIndex::Position(index) => index,
                }
            } else {
                unreachable!("attempt to access a field of a non-struct or tuple type")
            }
        })
    }
}
