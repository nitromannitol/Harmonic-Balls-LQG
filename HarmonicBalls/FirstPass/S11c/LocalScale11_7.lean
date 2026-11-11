import HarmonicBalls.Draft.Section11

/-!
# Lemma 11.7: scale and restriction invariance of the cone-mass event

For a deterministic disk `D` and a scalar `c ∈ (0,∞)`, the measure `c • μ|_D` agrees with `μ` on the closed ball
`B̄_{6r}(z) ⊆ D` up to the factor `c`. The cone-mass event at `(r,z)` for the scaled restricted measure is therefore the
cone-mass event for `μ` at `(r,z)`, with the same threshold `M`. Also: the threshold `2M` event implies the threshold `M`
event (`M ≤ M'`), used to pass from the origin input at threshold `2M` to the Draft threshold `M`.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- The extended Green potential supremum of `c • μ|_D` over the annulus `𝔸_{3r,6r}(z)` is `c` times that of `μ`, when
the closed ball `B̄_{6r}(z)` lies in the measurable set `D` (the annulus integrals only see `μ` on `B̄_{6r}(z)`). -/
theorem annulusGreenPotentialSup_smul_restrict (μ : Measure ℂ) {D : Set ℂ} (hDm : MeasurableSet D) (c : ℝ≥0∞)
    (z : ℂ) (r : ℝ) (hD : closedBall z (6 * r) ⊆ D) :
    annulusGreenPotentialSup (c • μ.restrict D) z (3 * r) (6 * r) = c * annulusGreenPotentialSup μ z (3 * r) (6 * r) := by
  have hA : annulus z (3 * r) (6 * r) ⊆ D := fun y hy => hD (Metric.ball_subset_closedBall hy.1)
  unfold annulusGreenPotentialSup
  simp only [ENNReal.mul_iSup]
  refine iSup_congr fun x => iSup_congr fun _ => ?_
  rw [Measure.restrict_smul, lintegral_smul_measure, Measure.restrict_restrict' hDm, Set.inter_eq_left.mpr hA, smul_eq_mul]

/-- The cone-mass event for the scaled restricted measure `c • μ|_D` is the cone-mass event for `μ` at `(r,z)`, when
`c ∈ (0,∞)` and `B̄_{6r}(z) ⊆ D` (paper (4.3): both the sector mass and the extended potential multiply by `c`). -/
theorem coneMassEvent_smul_restrict_iff (μ : Measure ℂ) {D : Set ℂ} (hDm : MeasurableSet D) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcT : c ≠ ⊤) (Q : Set ℂ) (M r : ℝ) (hr : 0 ≤ r) (z : ℂ) (hD : closedBall z (6 * r) ⊆ D) :
    coneMassEvent (c • μ.restrict D) Q M r z ↔ coneMassEvent μ Q M r z := by
  have hsub : annulus z r (2 * r) ∩ coneAt Q z ⊆ D := fun y hy =>
    hD (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hy.1.1))
  have hS : (c • μ.restrict D) (annulus z r (2 * r) ∩ coneAt Q z) = c * μ (annulus z r (2 * r) ∩ coneAt Q z) := by
    rw [Measure.smul_apply, Measure.restrict_apply' hDm, Set.inter_eq_left.mpr hsub, smul_eq_mul]
  unfold coneMassEvent
  rw [annulusGreenPotentialSup_smul_restrict μ hDm c z r hD, hS, ← mul_assoc, mul_comm (ENNReal.ofReal M) c, mul_assoc]
  exact ENNReal.mul_le_mul_iff_right hc0 hcT

/-- The threshold `M'` event implies the threshold `M` event when `0 ≤ M ≤ M'`: the cone-mass event is monotone in the
threshold (the extended potential is nonnegative in `ENNReal`). Used to pass from the origin input at `2M` to the Draft `M`. -/
theorem coneMassEvent_of_threshold_le (μ : Measure ℂ) (Q : Set ℂ) {M M' : ℝ} (hMM' : M ≤ M')
    (r : ℝ) (z : ℂ) (h : coneMassEvent μ Q M' r z) : coneMassEvent μ Q M r z :=
  le_trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hMM') zero_le) h

end HarmonicBalls.S11c
