import HarmonicBalls.Proofs.Sec9.CorrectedSubharmonicUniqueness

/-!
# Limits of disc Green circle averages

Shrinking circle averages increase to the extended Green kernel.
-/

namespace HarmonicBalls

open Metric Filter Topology Set

/-- Circle averages along shrinking positive radii increase to the extended disc Green value. -/
theorem circleAverage_greenFunction_ball_monotone_tendsto
    {R : ℝ} {x y : ℂ} {r : ℕ → ℝ}
    (hx : x ∈ ball (0 : ℂ) R) (hy : y ∈ ball (0 : ℂ) R)
    (hr : ∀ n, 0 < r n) (hanti : Antitone r) (hrlim : Tendsto r atTop (𝓝 0))
    (hsub : ∀ n, closedBall x (r n) ⊆ ball 0 R) :
    Monotone (fun n => ENNReal.ofReal (Real.circleAverage (greenFunction (ball 0 R) y) x (r n))) ∧
    Tendsto (fun n => ENNReal.ofReal (Real.circleAverage (greenFunction (ball 0 R) y) x (r n)))
      atTop (𝓝 (if x = y then ⊤ else ENNReal.ofReal (greenFunction (ball 0 R) y x))) := by
  have hc : 0 < (2 * Real.pi)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  constructor
  · intro i j hij
    apply ENNReal.ofReal_le_ofReal
    rw [circleAverage_greenFunction_ball_eq_log_max (hr i) hy (hsub i),
      circleAverage_greenFunction_ball_eq_log_max (hr j) hy (hsub j)]
    have hm : max (r j) ‖y - x‖ ≤ max (r i) ‖y - x‖ := max_le_max (hanti hij) le_rfl
    have hp : 0 < max (r j) ‖y - x‖ := (hr j).trans_le (le_max_left _ _)
    have hl := Real.log_le_log hp hm
    nlinarith
  · by_cases hxy : x = y
    · subst y
      simp only [↓reduceIte]
      apply ENNReal.tendsto_ofReal_nhds_top.mpr
      have hrgt : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r hrlim
          (Filter.Eventually.of_forall hr)
      have hlog : Tendsto (fun n => Real.log (r n)) atTop atBot :=
        Real.tendsto_log_nhdsGT_zero.comp hrgt
      have hdiv : Tendsto (fun n => -(2 * Real.pi)⁻¹ * Real.log (r n) -
          greatestHarmonicMinorantBall R x x) atTop atTop := by
        have h := hlog.atBot_mul_const_of_neg (neg_lt_zero.mpr hc)
        have h' := tendsto_atTop_add_const_right atTop
          (-greatestHarmonicMinorantBall R x x) h
        simpa only [mul_comm, sub_eq_add_neg] using h'
      apply hdiv.congr'
      filter_upwards [] with n
      rw [circleAverage_greenFunction_ball_eq_log_max (hr n) hy (hsub n)]
      simp [max_eq_left (hr n).le]
    · simp only [hxy, ↓reduceIte]
      have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
      have hev : ∀ᶠ n in atTop, r n < ‖y - x‖ := hrlim.eventually (Iio_mem_nhds hd)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with n hn
      rw [circleAverage_greenFunction_ball_eq_log_max (hr n) hy (hsub n),
        max_eq_right hn.le, greenFunction_ball_eq_sub hy hx (Ne.symm hxy), newtonKernel]

end HarmonicBalls
