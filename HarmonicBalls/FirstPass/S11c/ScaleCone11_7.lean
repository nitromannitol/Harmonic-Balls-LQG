import HarmonicBalls.Draft.Section11

/-!
# Lemma 11.7, scale invariance of the cone-mass event (deterministic)

`coneMassEvent μ Q M r z` (Draft/Section11.lean:72) compares `M · annulusGreenPotentialSup μ z (3r) (6r)` with the mass
`μ(annulus z r (2r) ∩ coneAt Q z)`. Both sides are linear in `μ`, so the event is unchanged under a multiplication of
the measure by a constant `c ∈ (0, ∞)`. This is used for the LQG measure, which is determined only up to a positive
constant by the constant shift of the circle averages (Translate11_7.lean, `isLQGLimit_sub_const`).
-/

open MeasureTheory Filter Metric Set
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- The annulus Green potential is linear in the measure: `annulusGreenPotentialSup (c • μ) = c · annulusGreenPotentialSup μ`
(Defs/Annuli.lean:65, a supremum of lower integrals). -/
lemma annulusGreenPotentialSup_smul (μ : Measure ℂ) (c : ℝ≥0∞) (x₀ : ℂ) (a b : ℝ) :
    annulusGreenPotentialSup (c • μ) x₀ a b = c * annulusGreenPotentialSup μ x₀ a b := by
  unfold annulusGreenPotentialSup
  simp only [Measure.restrict_smul, lintegral_smul_measure, ENNReal.mul_iSup, smul_eq_mul]

/-- The cone-mass event is invariant under multiplication of the measure by a constant `c ∈ (0, ∞)`. -/
theorem coneMassEvent_smul_iff (μ : Measure ℂ) (Q : Set ℂ) (M r : ℝ) (z : ℂ) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ⊤) :
    coneMassEvent (c • μ) Q M r z ↔ coneMassEvent μ Q M r z := by
  unfold coneMassEvent
  rw [annulusGreenPotentialSup_smul, Measure.smul_apply, smul_eq_mul, mul_left_comm]
  exact ENNReal.mul_le_mul_iff_right hc0 hc

end HarmonicBalls.S11c
