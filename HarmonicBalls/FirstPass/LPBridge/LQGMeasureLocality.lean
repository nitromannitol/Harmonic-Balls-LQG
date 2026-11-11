import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived
import HarmonicBalls.LPStage.LQGMeasureLocality
import HarmonicBalls.Proposed.LQG

/-!
# LP-stage bridge for the locality of the LQG measure (z3)

`HarmonicBalls.lqgMeasureLocality_of_lpStage` is the HB Proposed input `LQGMeasureLocality` (`Proposed/LQG.lean:97`,
Fact 2.1 II), obtained from the LP statement `LatticeProb.LQG.lqgLocality_of_circleLink` (`LPStage/LQGMeasureLocality.lean`)
through the bridge equivalences of `FirstPass/LPBridge/M1.lean` and `M4.lean`.

The LP statement is conditional on the circle-average link `LQGCircleAverageLink`. That link is discharged here by the HB
derivation `HarmonicBalls.lqgCircleAverageLocalityLink_derived` (`FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean`,
z6 dc3897c3). So this bridge is binder-free and uses no input beyond the HB derivation already in the repository.
-/

namespace HarmonicBalls

open MeasureTheory
open LPBridge

universe u

/-- `LQGMeasureLocality` (`Proposed/LQG.lean:97`) from the LP stage: `lqgLocality_of_circleLink` with its circle-average
link discharged by `lqgCircleAverageLocalityLink_derived`. Binder-free. -/
theorem lqgMeasureLocality_of_lpStage (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : LQGMeasureLocality P γ α₀ hC hcirc := by
  unfold LQGMeasureLocality
  intro hGFF hγ hγ2 hα μ hμ U hU
  have hLP := LatticeProb.LQG.lqgLocality_of_circleLink P γ α₀ hC hcirc
    (fun hG U' hU' r z hr hsub =>
      lqgCircleAverageLocalityLink_derived P α₀ hC hcirc ((isWholePlaneGFF_iff P hC hcirc).2 hG) U' hU' r z hr hsub)
  exact hLP ((isWholePlaneGFF_iff P hC hcirc).1 hGFF) hγ hγ2 hα μ
    ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ) U hU

end HarmonicBalls
