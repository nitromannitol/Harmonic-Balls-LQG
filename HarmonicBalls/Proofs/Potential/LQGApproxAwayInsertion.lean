import LatticeProb.LQG.GMCDilationField

/-!
# Comparison of approximation masses away from the insertion

On bounded sets at positive distance from the insertion, the logarithmic
weight is bounded uniformly over regularization scales at most one.
-/

open MeasureTheory Metric Set

namespace HarmonicBalls

open LatticeProb.LQG LatticeProb.Gauss

/-- Compare singular and ordinary approximation masses uniformly in the
regularization scale on a bounded measurable set away from the origin. -/
theorem singular_approximant_apply_le_ordinary
    {γ α ε d R : ℝ} (hγ : 0 ≤ γ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hd : 0 < d) (h : ℝ → ℂ → ℝ) {A : Set ℂ} (hA : MeasurableSet A)
    (hA_bounds : ∀ z ∈ A, d ≤ ‖z‖ ∧ ‖z‖ ≤ R) :
    lqgApprox γ (fieldCircleAverage α h) ε A ≤
      ENNReal.ofReal (Real.exp (γ * (|α| *
        (|Real.log d| + |Real.log (max 1 R)|)))) * lqgApprox γ h ε A := by
  apply lqgApprox_apply_le_of_le_add hγ hε.le hA
  intro z hz
  obtain ⟨hzlo, hzhi⟩ := hA_bounds z hz
  have hlo : d ≤ max ε ‖z‖ := hzlo.trans (le_max_right _ _)
  have hhi : max ε ‖z‖ ≤ max 1 R := max_le_max hε1 hzhi
  have hloglo : Real.log d ≤ Real.log (max ε ‖z‖) :=
    Real.log_le_log hd hlo
  have hloghi : Real.log (max ε ‖z‖) ≤ Real.log (max 1 R) :=
    Real.log_le_log (lt_of_lt_of_le hd hlo) hhi
  have hlog : |Real.log (max ε ‖z‖)| ≤
      |Real.log d| + |Real.log (max 1 R)| := by
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le (Real.log d), le_abs_self (Real.log (max 1 R)), abs_nonneg (Real.log d), abs_nonneg (Real.log (max 1 R))]
  have hprod : |α * Real.log (max ε ‖z‖)| ≤
      |α| * (|Real.log d| + |Real.log (max 1 R)|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hlog (abs_nonneg α)
  have hc : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z ε =
      Real.log (max ε ‖z‖) := by
    simpa only [sub_zero] using circleAverage_log_norm_sub_eq_log_max hε z 0
  simp only [fieldCircleAverage, hc]
  linarith [neg_abs_le (α * Real.log (max ε ‖z‖))]

/-- A uniform ordinary power bound transfers to singular approximations on
balls whose centers stay away from the origin. The ordinary bound is assumed. -/
theorem singular_approximant_ball_le_of_ordinary
    {γ α d R C β : ℝ} (hγ : 0 ≤ γ) (hd : 0 < d)
    (h : ℝ → ℂ → ℝ) (S : Set ℝ)
    (hbound : ∀ (ε : ℝ), ε ∈ S → 0 < ε → ε ≤ 1 → ∀ (z : ℂ), ‖z‖ ≤ R →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        lqgApprox γ h ε (ball z r) ≤ ENNReal.ofReal (C * r ^ β)) :
    ∀ (ε : ℝ), ε ∈ S → 0 < ε → ε ≤ 1 → ∀ (z : ℂ), 2 * d ≤ ‖z‖ → ‖z‖ ≤ R →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 → r ≤ d →
        lqgApprox γ (fieldCircleAverage α h) ε (ball z r) ≤
          ENNReal.ofReal (Real.exp (γ * (|α| *
            (|Real.log d| + |Real.log (max 1 (R + 1))|)))) *
              ENNReal.ofReal (C * r ^ β) := by
  intro ε hεS hε hε1 z hzlo hzhi r hr hr1 hrd
  refine (singular_approximant_apply_le_ordinary (R := R + 1) hγ hε hε1 hd h measurableSet_ball ?_).trans ?_
  · intro w hw
    have hwz : ‖w - z‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
    have htri := norm_add_le (w - z) z
    rw [sub_add_cancel] at htri
    have htri' := norm_add_le (z - w) w
    rw [sub_add_cancel] at htri'
    have heq : ‖z - w‖ = ‖w - z‖ := norm_sub_rev _ _
    constructor <;> linarith
  · gcongr
    exact hbound ε hεS hε hε1 z hzhi r hr hr1

end HarmonicBalls
