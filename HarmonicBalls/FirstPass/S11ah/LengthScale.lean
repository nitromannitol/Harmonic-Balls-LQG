import HarmonicBalls.FirstPass.S11ah.LengthTransport

/-!
# Scaling of a local length metric (fp-S11ah-11-13-steps-4-5b, owner n4; wave 31)

The decoder output is `b · internalMetric(·, B)` with a random constant `b > 0` (LocalMetricReplacementStmt (18)).
This file shows that `b · D` is again `IsLengthMetricOn B` when `D` is, and the scaling identity of internal metrics.
-/

open MeasureTheory Metric Set Filter Topology HarmonicBalls
open scoped ENNReal

noncomputable section

namespace FirstPassS11ah

lemma curveLength_const_mul {b : ℝ} (hb : 0 ≤ b) (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) (s t : ℝ) :
    curveLength (fun x y => b * D x y) p s t = ENNReal.ofReal b * curveLength D p s t := by
  unfold curveLength
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun q => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ENNReal.ofReal_mul hb

lemma pathLength_const_mul {b : ℝ} (hb : 0 ≤ b) (D : ℂ → ℂ → ℝ) {x y : ℂ} (P : Path x y) :
    pathLength (fun u v => b * D u v) P = ENNReal.ofReal b * pathLength D P :=
  curveLength_const_mul hb D P.extend 0 1

lemma internalMetric_const_mul {b : ℝ} (hb : 0 < b) (D : ℂ → ℂ → ℝ) (U : Set ℂ) (x y : ℂ) :
    internalMetric (fun u v => b * D u v) U x y = ENNReal.ofReal b * internalMetric D U x y := by
  have h0 : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.2 hb).ne'
  have htop : ENNReal.ofReal b ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold internalMetric
  simp only [pathLength_const_mul hb.le]
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  simp only [ENNReal.mul_iInf_of_ne h0 htop]

/-- Scaling by a positive constant preserves the length metric property on a set `B`. -/
theorem IsLengthMetricOn.const_mul {B : Set ℂ} {D : ℂ → ℂ → ℝ} (hD : IsLengthMetricOn B D) {b : ℝ}
    (hb : 0 < b) : IsLengthMetricOn B (fun x y => b * D x y) where
  self_eq_zero z hz := by
    show b * D z z = 0
    rw [hD.self_eq_zero z hz, mul_zero]
  eq_of_eq_zero z hz w hw h := by
    refine hD.eq_of_eq_zero z hz w hw ?_
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd h1 hb.ne'
    · exact h1
  symm z hz w hw := by
    show b * D z w = b * D w z
    rw [hD.symm z hz w hw]
  triangle x hx y hy z hz := by
    show b * D x z ≤ b * D x y + b * D y z
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hD.triangle x hx y hy z hz) hb.le
  continuousOn := ContinuousOn.mul continuousOn_const hD.continuousOn
  isOpen_iff U hU := by
    rw [hD.isOpen_iff U hU]
    constructor
    · intro H z hz
      obtain ⟨ε, hε, H'⟩ := H z hz
      exact ⟨b * ε, mul_pos hb hε, fun w hw h => H' w hw (lt_of_mul_lt_mul_left h hb.le)⟩
    · intro H z hz
      obtain ⟨ε, hε, H'⟩ := H z hz
      exact ⟨ε / b, div_pos hε hb, fun w hw h => H' w hw (by rw [mul_comm]; exact (lt_div_iff₀ hb).1 h)⟩
  ofReal_eq_internalMetric z hz w hw := by
    show ENNReal.ofReal (b * D z w) = internalMetric (fun u v => b * D u v) B z w
    rw [internalMetric_const_mul hb, ENNReal.ofReal_mul hb.le, hD.ofReal_eq_internalMetric z hz w hw]

end FirstPassS11ah

end
