import HarmonicBalls.FirstPass.Frozen.S11e
import HarmonicBalls.FirstPass.Frozen.S11k
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M5a
import HarmonicBalls.FirstPass.LPBridge.M5b
import HarmonicBalls.LPStage.LQGMetricMeasurable2

/-!
# LP-stage bridge for the inner measurability of the LQG metric

* `HarmonicBalls.lqgMetricPointwiseAEMeasurable_of_lp`: the HB frozen Prop `LQGMetricPointwiseAEMeasurableFrozen`
  (`FirstPass/Frozen/S11e.lean:27`), from the LP theorem `LatticeProb.LQG.lqgMetricPointwiseAEMeasurable_lp`
  (`LPStage/LQGMetricMeasurable2.lean`).
* `HarmonicBalls.lqgInternalDiamInnerMeasurable_of_lp`: the HB frozen Prop `LQGInternalDiamInnerMeasurableFrozen`
  (`FirstPass/Frozen/S11k.lean:89`, row 32), from `LatticeProb.LQG.lqgInternalDiamInnerMeasurable_lp`.

The only hypothesis of each bridge is the HB literature input `LQGMetricFieldAxioms` (`Proposed/LQG.lean`) in the
quantified form used by the HB derivations (`lqgMetricPointwiseAEMeasurable_derived`,
`lqgInternalDiamInnerMeasurable_derived`). It is transported to the LP copy by `lqgMetricFieldAxioms_iff`
(`FirstPass/LPBridge/M5b.lean`); the field data by `isWholePlaneGFF_iff` (`M1`) and `isLQGMetricOfField_iff` (`M5b`).
No counted theorem is changed, and no literature content is asserted here.
-/

namespace HarmonicBalls

open MeasureTheory
open LPBridge

universe u

/-- `LQGMetricPointwiseAEMeasurableFrozen` (`FirstPass/Frozen/S11e.lean:27`) from the LP stage, given the HB input
`LQGMetricFieldAxioms` in its quantified form. -/
theorem lqgMetricPointwiseAEMeasurable_of_lp
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    LQGMetricPointwiseAEMeasurableFrozen := by
  intro γ ξ Ω mΩ P _ hC hcirc D hW hγ hγ2 hD x y
  exact LatticeProb.LQG.lqgMetricPointwiseAEMeasurable_lp
    (fun γ ξ α₀ Ω _ P hC hcirc => (lqgMetricFieldAxioms_iff P γ ξ α₀ hC hcirc).1 (hFA γ ξ α₀ Ω P hC hcirc))
    γ ξ Ω P hC hcirc D ((isWholePlaneGFF_iff P hC hcirc).1 hW) hγ hγ2
    ((isLQGMetricOfField_iff P γ ξ 0 hC D).1 hD) x y

/-- `LQGInternalDiamInnerMeasurableFrozen` (`FirstPass/Frozen/S11k.lean:89`, row 32) from the LP stage, given the HB
input `LQGMetricFieldAxioms` in its quantified form. -/
theorem lqgInternalDiamInnerMeasurable_of_lp
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    LQGInternalDiamInnerMeasurableFrozen.{u} := by
  intro γ ξ α₀ Ω _ P _ hC hcirc D hW h0 h1 h2 hD δ A hδ hA
  exact LatticeProb.LQG.lqgInternalDiamInnerMeasurable_lp.{u}
    (fun γ ξ α₀ Ω _ P hC hcirc => (lqgMetricFieldAxioms_iff P γ ξ α₀ hC hcirc).1 (hFA γ ξ α₀ Ω P hC hcirc))
    γ ξ α₀ Ω P hC hcirc D ((isWholePlaneGFF_iff P hC hcirc).1 hW) h0 h1 h2
    ((isLQGMetricOfField_iff P γ ξ α₀ hC D).1 hD) δ A hδ hA

end HarmonicBalls
