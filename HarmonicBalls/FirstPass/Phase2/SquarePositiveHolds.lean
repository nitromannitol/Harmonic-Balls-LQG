import HarmonicBalls.FirstPass.Phase2.SquarePositiveDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs29
import HarmonicBalls.FirstPass.Phase2.BallMassBoundsHolds
import HarmonicBalls.FirstPass.Phase2.CoordChangeZeroHolds
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# Positivity, full support and volume growth of the LQG measure, without hypotheses

The Ding-Gwynne ball-mass bounds (`wholePlaneLQGBallMassBounds_holds`), the coordinate change rule at `α₀ = 0`
(`lqgMeasureCoordChange_zero_holds`) and the existence of the γ-LQG measure of a whole-plane GFF with an `α`-log
singularity (`lqgMeasureExistence_forall_field`) hold for every model in universe `u`. The existing reductions from
these three facts therefore give, with no hypothesis:

* `lqgMeasureSquarePositiveFrozen_holds`: every closed dyadic square has positive `μ_h`-mass almost surely;
* `lqgMeasureFullSupportStmt_holds`: `μ_h` has full support almost surely (the input I1);
* `lqgVolumeGrowthAllScalesStmt_holds`: `r^{β⁻} ≤ μ_h(B_r(z)) ≤ r^{β⁺}` at all small scales (the input I2,
  `eq:volume-growth`).
-/

namespace HarmonicBalls

universe u

/-- Every closed dyadic square has positive LQG mass almost surely, for every model in universe `u`. -/
theorem lqgMeasureSquarePositiveFrozen_holds : LQGMeasureSquarePositiveFrozen.{u} :=
  lqgMeasureSquarePositiveFrozen_derived wholePlaneLQGBallMassBounds_holds.{u}
    lqgMeasureCoordChange_zero_holds.{u} lqgMeasureExistence_forall_field.{u}

/-- The γ-LQG measure of a whole-plane GFF has full support almost surely (the input I1). -/
theorem lqgMeasureFullSupportStmt_holds : LQGMeasureFullSupportStmt.{u} :=
  lqgMeasureFullSupportStmt_of_rows123 wholePlaneLQGBallMassBounds_holds.{u}
    lqgMeasureCoordChange_zero_holds.{u} lqgMeasureExistence_forall_field.{u}

/-- Polynomial volume growth of the γ-LQG measure at all small scales (the input I2, `eq:volume-growth`). -/
theorem lqgVolumeGrowthAllScalesStmt_holds : LQGVolumeGrowthAllScalesStmt.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_rows123 wholePlaneLQGBallMassBounds_holds.{u}
    lqgMeasureCoordChange_zero_holds.{u} lqgMeasureExistence_forall_field.{u}

end HarmonicBalls
