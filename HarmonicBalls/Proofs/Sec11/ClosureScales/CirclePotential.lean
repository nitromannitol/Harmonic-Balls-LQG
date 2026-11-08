import Mathlib

/-! # Route (A): the logarithmic potential of a uniform circle measure

For `r > 0` and `a, c ∈ ℂ`, the average of `log ‖· - a‖` over the circle of centre `c` and radius `r` is
`log max(r, ‖a - c‖)`: the logarithmic potential of the uniform probability on the circle, evaluated at `a`
(Armitage-Gardiner, potential theory on the plane). It is the circle-average identity behind the log-insertion limit
of the circle-code step (r10 `l:r9-circle-code`, proof). It follows from Mathlib's unit-circle identity
`circleAverage_log_norm_sub_const_eq_posLog` by rescaling, and an almost-everywhere replacement at the single
point where the rescaled integrand is singular. -/

noncomputable section

open Metric Set Filter Topology

namespace HarmonicBalls

/-- The circle average of `log ‖· - a‖` over the circle of centre `c` and radius `r > 0` is `log max(r, ‖a - c‖)`. -/
theorem circleAverage_log_norm_sub_eq_log_max {c a : ℂ} {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun y : ℂ => Real.log ‖y - a‖) c r = Real.log (max r ‖a - c‖) := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = (r : ℂ)⁻¹ * (a - c) := ⟨_, rfl⟩
  have hrb : (r : ℂ) * b = a - c := by
    rw [hb, ← mul_assoc, mul_inv_cancel₀ hrC, one_mul]
  -- the rescaled integrand equals `log r + log ‖· - b‖` off the single point `b`
  have hae : (fun z : ℂ => Real.log ‖(r : ℂ) * z + c - a‖) =ᶠ[codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|)]
      (fun z : ℂ => Real.log r + Real.log ‖z - b‖) := by
    have hnb : ∀ x : ℂ, ∀ᶠ y in 𝓝[≠] x, y ≠ b := by
      intro x
      by_cases hx : x = b
      · rw [hx]
        exact eventually_nhdsWithin_of_forall fun y hy => hy
      · exact (eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds
    have hc : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|), z ≠ b :=
      eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.2 fun x _ => (hnb x).mono fun y hy _ => hy
    filter_upwards [hc] with z hz
    have hzb : ‖z - b‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hz)
    have hfac : (r : ℂ) * z + c - a = (r : ℂ) * (z - b) := by
      linear_combination hrb
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, Real.log_mul hr.ne' hzb]
  rw [Real.circleAverage_eq_circleAverage_zero_one, Real.circleAverage_congr_codiscreteWithin hae one_ne_zero]
  -- split off the constant `log r`
  have hconst : CircleIntegrable (fun _ : ℂ => Real.log r) 0 1 := circleIntegrable_const (Real.log r) 0 1
  have hlog : CircleIntegrable (fun z : ℂ => Real.log ‖z - b‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  have hsplit : Real.circleAverage (fun z : ℂ => Real.log r + Real.log ‖z - b‖) 0 1 =
      Real.log r + Real.circleAverage (fun z : ℂ => Real.log ‖z - b‖) 0 1 := by
    have h := Real.circleAverage_fun_add hconst hlog
    rw [Real.circleAverage_const] at h
    exact h
  rw [hsplit, circleAverage_log_norm_sub_const_eq_posLog]
  -- the unit-circle average is `log⁺ ‖b‖`, and `‖b‖ = ‖a - c‖ / r`
  have hnorm : ‖b‖ = ‖a - c‖ / r := by
    rw [hb, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le]
    ring
  rw [hnorm, Real.posLog]
  rcases eq_or_lt_of_le (norm_nonneg (a - c)) with h0 | hpos
  · rw [← h0, max_eq_left hr.le]
    simp
  · rw [Real.log_div hpos.ne' hr.ne']
    rcases le_total r ‖a - c‖ with h | h
    · rw [max_eq_right h, max_eq_right (show 0 ≤ Real.log ‖a - c‖ - Real.log r from
        sub_nonneg.2 (Real.log_le_log hr h))]
      ring
    · rw [max_eq_left h, max_eq_left (show Real.log ‖a - c‖ - Real.log r ≤ 0 from
        sub_nonpos.2 (Real.log_le_log hpos h))]
      ring

end HarmonicBalls

end
