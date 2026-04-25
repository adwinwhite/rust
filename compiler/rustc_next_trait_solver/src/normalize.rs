use rustc_type_ir::data_structures::ensure_sufficient_stack;
use rustc_type_ir::inherent::*;
use rustc_type_ir::solve::{Goal, NoSolution};
use rustc_type_ir::{
    self as ty, Binder, FallibleTypeFolder, InferCtxtLike, Interner, TypeFoldable,
    TypeSuperFoldable, TypeVisitableExt, UniverseIndex,
};
use tracing::instrument;

use crate::placeholder::{BoundVarReplacer, PlaceholderReplacer};

/// This folder normalizes value and collects ambiguous goals.
///
/// Note that for ambiguous alias which contains escaping bound vars,
/// we just return the original alias and don't collect the ambiguous goal.
pub struct NormalizationFolder<'a, Infcx, I, F>
where
    Infcx: InferCtxtLike<Interner = I>,
    I: Interner,
{
    infcx: &'a Infcx,
    universes: Vec<Option<UniverseIndex>>,
    stalled_goals: Vec<Goal<I, I::Predicate>>,
    normalize: F,
}

#[derive(PartialEq, Eq)]
enum HasEscapingBoundVars {
    Yes,
    No,
}

impl<'a, Infcx, I, F> NormalizationFolder<'a, Infcx, I, F>
where
    Infcx: InferCtxtLike<Interner = I>,
    I: Interner,
    F: FnMut(I::Term) -> Result<(I::Term, Option<Goal<I, I::Predicate>>), NoSolution>,
{
    pub fn new(
        infcx: &'a Infcx,
        universes: Vec<Option<UniverseIndex>>,
        stalled_goals: Vec<Goal<I, I::Predicate>>,
        normalize: F,
    ) -> Self {
        Self { infcx, universes, stalled_goals, normalize }
    }

    pub fn stalled_goals(self) -> Vec<Goal<I, I::Predicate>> {
        self.stalled_goals
    }

    fn normalize_alias_term(
        &mut self,
        alias_term: I::Term,
        has_escaping: HasEscapingBoundVars,
    ) -> Result<I::Term, NoSolution> {
        let (normalized, ambig_goal) = (self.normalize)(alias_term)?;

        // Return ambiguous higher ranked alias as is if it contains escaping vars.
        // We can normalize it again after the binder is instantiated.
        if ambig_goal.is_some() && has_escaping == HasEscapingBoundVars::Yes {
            return Ok(alias_term);
        }

        self.stalled_goals.extend(ambig_goal);
        Ok(normalized)
    }
}

impl<'a, Infcx, I, F> FallibleTypeFolder<I> for NormalizationFolder<'a, Infcx, I, F>
where
    Infcx: InferCtxtLike<Interner = I>,
    I: Interner,
    F: FnMut(I::Term) -> Result<(I::Term, Option<Goal<I, I::Predicate>>), NoSolution>,
{
    type Error = NoSolution;

    fn cx(&self) -> I {
        self.infcx.cx()
    }

    fn try_fold_binder<T: TypeFoldable<I>>(
        &mut self,
        t: Binder<I, T>,
    ) -> Result<Binder<I, T>, Self::Error> {
        self.universes.push(None);
        let t = t.try_super_fold_with(self)?;
        self.universes.pop();
        Ok(t)
    }

    #[instrument(level = "trace", skip(self), ret)]
    fn try_fold_ty(&mut self, ty: I::Ty) -> Result<I::Ty, Self::Error> {
        let infcx = self.infcx;
        if !ty.has_aliases() {
            return Ok(ty);
        }

        // With eager normalization, we should normalize the args of alias before
        // normalizing the alias itself.
        let ty = ty.try_super_fold_with(self)?;
        let ty::Alias(..) = ty.kind() else { return Ok(ty) };

        if ty.has_escaping_bound_vars() {
            let (ty, mapped_regions, mapped_types, mapped_consts) =
                BoundVarReplacer::replace_bound_vars(infcx, &mut self.universes, ty);
            let result = ensure_sufficient_stack(|| {
                self.normalize_alias_term(ty.into(), HasEscapingBoundVars::Yes)
            })?
            .expect_ty();
            Ok(PlaceholderReplacer::replace_placeholders(
                infcx,
                mapped_regions,
                mapped_types,
                mapped_consts,
                &self.universes,
                result,
            ))
        } else {
            Ok(ensure_sufficient_stack(|| {
                self.normalize_alias_term(ty.into(), HasEscapingBoundVars::No)
            })?
            .expect_ty())
        }
    }

    #[instrument(level = "trace", skip(self), ret)]
    fn try_fold_const(&mut self, ct: I::Const) -> Result<I::Const, Self::Error> {
        let infcx = self.infcx;
        if !ct.has_aliases() {
            return Ok(ct);
        }

        // With eager normalization, we should normalize the args of alias before
        // normalizing the alias itself.
        let ct = ct.try_super_fold_with(self)?;
        let ty::ConstKind::Unevaluated(..) = ct.kind() else { return Ok(ct) };

        if ct.has_escaping_bound_vars() {
            let (ct, mapped_regions, mapped_types, mapped_consts) =
                BoundVarReplacer::replace_bound_vars(infcx, &mut self.universes, ct);
            let result = ensure_sufficient_stack(|| {
                self.normalize_alias_term(ct.into(), HasEscapingBoundVars::Yes)
            })?
            .expect_const();
            Ok(PlaceholderReplacer::replace_placeholders(
                infcx,
                mapped_regions,
                mapped_types,
                mapped_consts,
                &self.universes,
                result,
            ))
        } else {
            Ok(ensure_sufficient_stack(|| {
                self.normalize_alias_term(ct.into(), HasEscapingBoundVars::No)
            })?
            .expect_const())
        }
    }
}
