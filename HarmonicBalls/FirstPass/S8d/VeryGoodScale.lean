import HarmonicBalls.Defs.Annuli

/-! # FIRST-PASS helper (fp-S8d, owner n4): positive constant multiples of very-good annuli

The very-good annulus event `IsVeryGoodAnnulus` (Defs/Annuli.lean:81) is invariant under multiplication of the
measure by a positive finite constant `c`: the annulus-ball mass size `annulusBallMassSize` (Defs/Annuli.lean:~92)
and the Green potential supremum `annulusGreenPotentialSup` (Defs/Annuli.lean:65) are multiplied by `c`, the
mass ratios in `IsVeryGoodAnnulus` cancel `c`, and the good-annulus event `IsGoodAnnulus` (Defs/Annuli.lean:47)
compares masses of sets, so `c` cancels there as well. The Brownian exit condition does not involve the measure.

This is the deterministic step that lets a Lemma 6.7 field whose LQG measure is determined only up to a deterministic
positive factor (the Weyl scaling by a constant, Proposed/LQG.lean:93) be compared with the normalized measure.
No new mathematics. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

variable {c : ℝ≥0∞}

/-- The annulus-ball mass size is multiplied by a positive finite constant. -/
theorem annulusBallMassSize_smul (μ : Measure ℂ) (hc0 : c ≠ 0) (hcT : c ≠ ∞) (βminus ρ : ℝ) (x₀ : ℂ) :
    annulusBallMassSize (c • μ) βminus ρ x₀ = c * annulusBallMassSize μ βminus ρ x₀ := by
  unfold annulusBallMassSize
  simp only [ENNReal.mul_iInf_of_ne hc0 hcT, Measure.smul_apply, smul_eq_mul, mul_div_assoc]

/-- The Green potential supremum is multiplied by a positive finite constant. -/
theorem annulusGreenPotentialSup_smul (μ : Measure ℂ) (x₀ : ℂ) (a b : ℝ) :
    annulusGreenPotentialSup (c • μ) x₀ a b = c * annulusGreenPotentialSup μ x₀ a b := by
  unfold annulusGreenPotentialSup
  simp only [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ENNReal.mul_iSup]

/-- The good-annulus event does not change under a positive finite constant multiple of the measure. -/
theorem isGoodAnnulus_smul_iff (μ : Measure ℂ) (hc0 : c ≠ 0) (hcT : c ≠ ∞) (r : ℝ) (z : ℂ) (a b : ℝ) :
    IsGoodAnnulus (c • μ) r z a b ↔ IsGoodAnnulus μ r z a b := by
  unfold IsGoodAnnulus
  have key : ∀ Y : Set ℂ, c * μ Y ≤ ENNReal.ofReal a * (c * μ (annulus z (3 * r) (5 * r))) ↔
      μ Y ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) := fun Y => by
    rw [show ENNReal.ofReal a * (c * μ (annulus z (3 * r) (5 * r)))
        = c * (ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))) by ring]
    exact ENNReal.mul_le_mul_iff_right hc0 hcT
  simp only [Measure.smul_apply, smul_eq_mul, key]

/-- The very-good annulus event is invariant under a positive finite constant multiple of the measure
(Defs/Annuli.lean:81). -/
theorem isVeryGoodAnnulus_smul_iff (μ : Measure ℂ) (hc0 : c ≠ 0) (hcT : c ≠ ∞) (βminus ρ : ℝ) (x₀ : ℂ)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    IsVeryGoodAnnulus (c • μ) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  unfold IsVeryGoodAnnulus
  simp only [annulusBallMassSize_smul μ hc0 hcT, annulusGreenPotentialSup_smul μ,
    Measure.smul_apply, smul_eq_mul, isGoodAnnulus_smul_iff μ hc0 hcT,
    ENNReal.mul_div_mul_left _ _ hc0 hcT]

#print axioms isVeryGoodAnnulus_smul_iff

end HarmonicBalls
