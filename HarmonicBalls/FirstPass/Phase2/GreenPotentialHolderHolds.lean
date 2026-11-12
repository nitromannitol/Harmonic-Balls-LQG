import HarmonicBalls.Proofs.Potential.GreenGeneralHolder
import HarmonicBalls.Proofs.Sec2.GreenPotentialGeneral
import HarmonicBalls.FirstPass.Phase2.BallMassBoundsHolds
import HarmonicBalls.FirstPass.Phase2.DerivedInputs29
import HarmonicBalls.FirstPass.Phase2.CoordChangeZeroHolds
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# The Green clause of Proposition 2.5 without hypotheses

`GreenPotentialHolderStmt` (almost surely, Green potentials of bounded densities against the
whole-plane LQG measure are absolutely convergent and Hölder continuous on the closure of every smooth
bounded open set) follows from the deterministic general-domain estimate
`greenPotentialGeneralStep_holds` and the volume growth of the LQG measure at all scales, which is
derived from the ball mass bounds, the coordinate change at scale zero and the existence of the LQG
measure.
-/

namespace HarmonicBalls

universe u

/-- The Green clause of Proposition 2.5, with no hypotheses. -/
theorem greenPotentialHolderStmt_holds : GreenPotentialHolderStmt.{u} :=
  greenPotentialHolderStmt_of_volumeGrowth greenPotentialGeneralStep_holds
    (lqgVolumeGrowthAllScalesStmt_of_rows123.{u} wholePlaneLQGBallMassBounds_holds.{u}
      lqgMeasureCoordChange_zero_holds.{u} lqgMeasureExistence_forall_field.{u})

end HarmonicBalls
