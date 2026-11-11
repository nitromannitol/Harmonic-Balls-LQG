import HarmonicBalls.Draft.Section2
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Annuli
import HarmonicBalls.Steps.Sec11.PinchGreenFinite

/-!
# Almost sure finiteness at insertion `α`

Let `0 < γ < 2`, `α < Q = lqgQ γ`, and let `μ` be the γ-LQG measure of the insertion-`α` field
`h = h^ℂ - α log|·|` (`IsLQGMeasureOfField P γ α hcirc μ`) of a whole-plane GFF. The decoded pinch rule
(`S11am.decodedPinchRule_iff`) needs two almost sure finiteness facts:

* `S = SG_{3,6}(μ) = annulusGreenPotentialSup μ 0 3 6 ≠ ∞`: the annular Green potential is finite under LQG volume growth (dyadic summation of the Green
  kernel bound against `μ(B_r(z)) ≤ r^{β⁺}`), `ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth`;
* `μ(U) ≠ ∞` for every bounded `U ⊆ ℂ`: local finiteness of the LQG limit (`IsLQGLimit`, Fact 2.1 I).

Inputs: only the frozen `LQGVolumeGrowthAllScalesStmt` (Input I2, `Draft/Section2.lean`, quantified over all
`α₀ < lqgQ γ`) enters the first statement. The second uses no input beyond `IsLQGMeasureOfField`.
-/

namespace HarmonicBalls.S11ay

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

/-- **Annular Green potential is almost surely finite at insertion `α`.** For the γ-LQG measure `μ` of the
insertion-`α` field of a whole-plane GFF, `0 < γ < 2`, `α < Q`, almost surely `S = SG_{3,6}(μ) ≠ ∞`. The Green
kernel is the one of `annulusGreenPotentialSup` (diagonal value `∞`). Input: the frozen `LQGVolumeGrowthAllScalesStmt`. -/
theorem ae_annulusGreenPotentialSup_ne_top_alpha {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ⊤ :=
  HarmonicBalls.ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth hgrowth hγ0 hγ2 hα hGFF hμ 3
    (by norm_num)

/-- **Local finiteness of the insertion-`α` LQG measure.** For every bounded `U ⊆ ℂ`, almost surely `μ(U) ≠ ∞`,
since `μ` is a locally finite measure almost surely (`IsLQGLimit`, Radon, Fact 2.1 I) and `closure U` is compact. -/
theorem ae_measure_ne_top_of_isBounded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (U : Set ℂ) (hU : Bornology.IsBounded U) :
    ∀ᵐ ω ∂P, μ ω U ≠ ⊤ := by
  filter_upwards [hμ] with ω hω
  have := hω.isLocallyFiniteMeasure
  have hfin : μ ω (closure U) < ⊤ := hU.isCompact_closure.measure_lt_top
  exact ((measure_mono subset_closure).trans_lt hfin).ne

end HarmonicBalls.S11ay
