import Mathlib

/-! # Subcritical exponents for Liouville clock estimates

The truncated second moment estimate in Berestycki, *Diffusion in planar Liouville quantum gravity*,
Section 2, admits strictly positive decay exponents throughout the subcritical range.
-/

namespace HarmonicBalls

/-- A truncation level and an occupation exponent can be chosen to make both the thin- and
thick-point decay exponents positive. -/
theorem exists_clock_truncation_exponents {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ α d : ℝ, γ < α ∧ α < 2 * γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ ^ 2 + (2 * γ - α) ^ 2 / 2 ∧ 0 < (α - γ) ^ 2 / 2 := by
  have hchoose : ∃ α : ℝ, γ < α ∧ α < 2 * γ ∧
      0 < 2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2 := by
    by_cases h : γ < 1
    · refine ⟨3 * γ / 2, by linarith, by linarith, ?_⟩
      have hm := mul_pos hγ0 (sub_pos.mpr h)
      nlinarith
    · refine ⟨(γ + 2) / 2, by linarith, by linarith, ?_⟩
      have hm := mul_pos (sub_pos.mpr hγ2) (show 0 < 10 - γ by linarith)
      nlinarith
  obtain ⟨α, hγα, hα, he⟩ := hchoose
  let e : ℝ := 2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2
  have he0 : 0 < e := he
  have he2 : e < 2 := by
    have hm := mul_pos (show 0 < α - γ by linarith) (show 0 < 3 * γ - α by linarith)
    dsimp [e]
    nlinarith
  refine ⟨α, 2 - e / 2, hγα, hα, by linarith, by linarith, ?_, ?_⟩
  · dsimp [e] at *
    linarith
  · positivity

open MeasureTheory Set
open scoped Interval

/-- The time-difference kernel occurring in a finite-horizon pair occupation estimate. -/
theorem integral_unit_triangle_rpow {q : ℝ} (hq : q < 1) :
    (∫ u in (0 : ℝ)..1, (1 - u) * u ^ (-q)) = 1 / ((1 - q) * (2 - q)) := by
  have h1 : IntervalIntegrable (fun u : ℝ => u ^ (-q)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h2 : IntervalIntegrable (fun u : ℝ => u ^ (1 - q)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have heq : (∫ u in (0 : ℝ)..1, (1 - u) * u ^ (-q)) =
      ∫ u in (0 : ℝ)..1, (u ^ (-q) - u ^ (1 - q)) := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := by simpa using hu.1
    rw [show 1 - q = 1 + (-q) by ring, Real.rpow_add hu0, Real.rpow_one]
    ring
  rw [heq, intervalIntegral.integral_sub h1 h2,
    integral_rpow (Or.inl (show -1 < -q by linarith)),
    integral_rpow (Or.inl (show -1 < 1 - q by linarith))]
  rw [Real.one_rpow, Real.one_rpow, Real.zero_rpow (by linarith : -q + 1 ≠ 0),
    Real.zero_rpow (by linarith : 1 - q + 1 ≠ 0)]
  have he1 : -q + 1 = 1 - q := by ring
  have he2 : 1 - q + 1 = 2 - q := by ring
  rw [he1, he2]
  have hn1 : 1 - q ≠ 0 := by linarith
  have hn2 : 2 - q ≠ 0 := by linarith
  field_simp [hn1, hn2]
  ring

end HarmonicBalls
