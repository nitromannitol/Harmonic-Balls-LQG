import HarmonicBalls.FirstPass.Frozen.S11d

/-!
# Proposition 11.9, Cameron-Martin transfer of positive probability (fp-S11d, owner n3)

FIRST-PASS NEW. The last step of `prop:mass-diam-gen` (corrected paper, line 3131): a positive-probability event for the
shifted field `h~ = h - (φ/ξ) log(2A/ε)` gives a positive-probability event for `h`, because the laws are mutually absolutely
continuous. Here the shifted field is the whole-plane GFF `hC + g` with `g = -(φ/ξ) c` (smooth, compactly supported, zero
unit-circle average since `φ = 0` on `∂B₁`); the input is the frozen `CameronMartinGFFMutualAbsCont`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory

/-- Positive probability transfers from the shifted field to the GFF along a measurable set of fields. -/
theorem cm_transfer_pos (hCM : CameronMartinGFFMutualAbsCont.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hgc : ContDiff ℝ (⊤ : ℕ∞) g) (hgs : HasCompactSupport g)
    (hg0 : Real.circleAverage g 0 1 = 0) {B : Set ((ℂ → ℝ) → ℝ)}
    (hB : MeasurableSet[distributionMeasurableSpace] B)
    (hpos : 0 < P ((fun ω => addFunPairing (hC ω) g) ⁻¹' B)) :
    0 < P ((fun ω => hC ω) ⁻¹' B) := by
  have h := hCM Ω P hC hcirc g hG hgc hgs hg0 B hB
  by_contra hle
  have h0 : P ((fun ω => hC ω) ⁻¹' B) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hle)
  exact hpos.ne' (h.mp h0)

end HarmonicBalls
