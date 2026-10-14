use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use tracing::instrument;

pub type SolverRegionConstraint<'tcx> =
    rustc_type_ir::region_constraint::RegionConstraint<TyCtxt<'tcx>, Span>;

pub type SolverLeafRegionConstraint<'tcx> =
    rustc_type_ir::region_constraint::LeafRegionConstraint<TyCtxt<'tcx>, Span>;

#[derive(Clone, Debug)]
pub(crate) struct SolverRegionConstraintStorage<'tcx> {
    whole: Option<SolverRegionConstraint<'tcx>>,
    // FIXME: This is only used for snapshot-based leak check. We should get
    // rid of that and remove/adjust this in the long term.
    // Since type outlives are ignored in leak check, we don't collect leaf
    // region constraints from destructuring type outlives, so only region
    // outlives are available.
    leafs: Vec<SolverLeafRegionConstraint<'tcx>>,
}

impl<'tcx> SolverRegionConstraintStorage<'tcx> {
    pub(crate) fn new() -> Self {
        Self { whole: None, leafs: vec![] }
    }

    pub(crate) fn get_constraint(&self) -> SolverRegionConstraint<'tcx> {
        match &self.whole {
            Some(v) => v.clone(),
            None => SolverRegionConstraint::new_true(),
        }
    }

    #[instrument(level = "debug", skip(self))]
    pub(crate) fn overwrite(&mut self, constraint: SolverRegionConstraint<'tcx>) {
        self.whole = Some(constraint);
    }

    pub(crate) fn pop_leaf(&mut self) -> Option<SolverLeafRegionConstraint<'tcx>> {
        self.leafs.pop()
    }

    pub(crate) fn push_leaf(&mut self, leaf: SolverLeafRegionConstraint<'tcx>) {
        self.leafs.push(leaf)
    }
}

#[cfg(test)]
mod tests;
