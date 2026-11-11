import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.LQGMeasureLocality2
import HarmonicBalls.Proposed.LQG

/-!
# LP-stage bridge for the locality of the LQG measure

`HarmonicBalls.lqgMeasureLocality_of_lpStage` is the HB Proposed input `LQGMeasureLocality` (`Proposed/LQG.lean:97`,
Fact 2.1 II), obtained from the unconditional LP statement `LatticeProb.LQG.lqgLocality_of_gff`
(`LPStage/LQGMeasureLocality2.lean`) through the bridge equivalences of `FirstPass/LPBridge/M1.lean` and `M4.lean`.

The LP statement carries no circle-average link hypothesis: the link is proved in LP stage by
`LatticeProb.LQG.lqgCircleAverageLink_of_gff` from the whole-plane GFF premise. So this bridge is binder-free and uses no
HB input beyond the bridge equivalences.
-/

namespace HarmonicBalls

open MeasureTheory
open LPBridge

universe u

/-- `LQGMeasureLocality` (`Proposed/LQG.lean:97`) from the LP stage: `lqgLocality_of_gff` (unconditional LP locality).
Binder-free. -/
theorem lqgMeasureLocality_of_lpStage (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : LQGMeasureLocality P γ α₀ hC hcirc := by
  unfold LQGMeasureLocality
  intro hGFF hγ hγ2 hα μ hμ U hU
  exact LatticeProb.LQG.lqgLocality_of_gff P γ α₀ hC hcirc ((isWholePlaneGFF_iff P hC hcirc).1 hGFF) hγ hγ2 hα μ
    ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ) U hU

end HarmonicBalls
