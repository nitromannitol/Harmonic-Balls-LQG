import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.LQGMeasureSquare
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived

/-!
# LP-stage bridge for the square measurability of the LQG area measure

`HarmonicBalls.lqgMeasureSquareMeasurable_of_lpStage` is the HB Prop `LQGMeasureSquareMeasurableFrozen`
(`FirstPass/Frozen/S11c.lean:117`), obtained from the LP general statement
`LatticeProb.LQG.aemeasurable_lqgMeasure_closedDyadicSquare` (`LatticeProb/LQG/LQGMeasureSquare.lean`) through the bridge
equivalences of `FirstPass/LPBridge/M1.lean` and `M4.lean`.

The only input is the locality of the γ-LQG measure, the Proposed input `LQGMeasureLocality` (Fact 2.1 II,
`Proposed/LQG.lean:97`), taken in its universally quantified form exactly as in
`HarmonicBalls.lqgMeasureSquareMeasurable_derived` (`FirstPass/Phase2/SquareMeasurableDerived.lean`). The Proposed input
remains pending operator source-check.
-/

namespace HarmonicBalls

open MeasureTheory Set
open LPBridge

universe u

/-- `LQGMeasureSquareMeasurableFrozen` (`Frozen/S11c.lean:117`) from the LP general statement, given the locality input
`hmeasure` (`LQGMeasureLocality`, Proposed, in its universally quantified form). -/
theorem lqgMeasureSquareMeasurable_of_lpStage
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality P γ α₀ hC hcirc) :
    LQGMeasureSquareMeasurableFrozen.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ S hS
  have hGFF' := (isWholePlaneGFF_iff P hC hcirc).1 hGFF
  have hμ' := (isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ
  have hloc : LatticeProb.LQG.LQGLocality P γ α₀ hC hcirc := by
    intro h1 h2 h3 h4 ν hν U hU
    exact hmeasure γ α₀ Ω P hC hcirc (((isWholePlaneGFF_iff P hC hcirc).2 h1)) h2 h3 h4 ν
      ((isLQGMeasureOfField_iff P γ α₀ hcirc ν).2 hν) U hU
  obtain ⟨n, j, k, hSeq⟩ := hS
  exact LatticeProb.LQG.aemeasurable_lqgMeasure_closedDyadicSquare hγ hγ2 hα hGFF' hμ' hloc
    ⟨n, j, k, hSeq⟩

/-- `LQGMeasureSquareMeasurableFrozen` (`Frozen/S11c.lean:117`), binder-free: `lqgMeasureSquareMeasurable_of_lpStage` with
the locality input discharged by `lqgMeasureLocality_derived` (`FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean`). -/
theorem lqgMeasureSquareMeasurable_of_lpStage_derived : LQGMeasureSquareMeasurableFrozen.{u} :=
  lqgMeasureSquareMeasurable_of_lpStage.{u} (fun γ α₀ Ω _ P hC hcirc =>
    lqgMeasureLocality_derived γ α₀ Ω P hC hcirc)

end HarmonicBalls
