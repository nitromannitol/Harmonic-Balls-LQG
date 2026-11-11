import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec11.Closure.MassDiameterInside

/-!
# Normalization of the square dyadic tail input (transfer obligation O1)

For a whole-plane GFF `h^ℂ` normalized so that its unit circle average vanishes (`IsWholePlaneGFF`,
`Defs/GFF.lean`; paper line 365), the threshold factor `e^{ξ h^ℂ_1(0)}` in `SquareDyadicTailInput` equals `1`
almost surely. The tail statement is therefore the statement for the normalized field `h_1(0) = 0` of Pfeffer
arXiv:2104.04020v3 Prop. 4.6. The Lean fact used is `IsWholePlaneGFF.ae_circleAverage_one_zero`.
This file proves nothing about the tail bound.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- The threshold factor `e^{ξ h^ℂ_1(0)}` of a whole-plane GFF is `1` almost surely. -/
theorem ofReal_exp_mul_circleAverage_one_zero_ae {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) :
    ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) = 1 := by
  filter_upwards [hh.ae_circleAverage_one_zero] with ω hω
  simp [hω]

/-- `SquareDyadicTailInput` for the normalized field: the same tail statement with threshold `b n` alone,
without the factor `e^{ξ h^ℂ_1(0)}`. -/
def NormalizedSquareDyadicTailInput (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (z : ℂ) (L : ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → ∃ (b : ℕ → ℝ≥0∞) (p : ℝ) (_ : 2 < p) (e : ℕ → ℝ), Tendsto e atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, b n < ENNReal.ofReal a) ∧
    (∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      P {ω | b n < dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n)))

/-- Under a whole-plane GFF the factor `e^{ξ h^ℂ_1(0)}` can be dropped from `SquareDyadicTailInput`. -/
theorem squareDyadicTailInput_iff_normalized {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (z : ℂ) (L : ℝ) :
    SquareDyadicTailInput P ξ hC hcirc 𝔇 z L ↔ NormalizedSquareDyadicTailInput P hC 𝔇 z L := by
  have hae := ofReal_exp_mul_circleAverage_one_zero_ae hh ξ
  have key : ∀ (b : ℝ≥0∞) (X : Ω → ℝ≥0∞),
      P {ω | b * ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) < X ω} = P {ω | b < X ω} := by
    intro b X
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hae] with ω hω
    simp [hω]
  unfold SquareDyadicTailInput NormalizedSquareDyadicTailInput
  simp only [key]


end HarmonicBalls
