import HarmonicBalls.FirstPass.S11q
import HarmonicBalls.FirstPass.S11s

/-!
# B1 scaling identities for the dilation by `r = 1/2` (fp-S11s-11-13-B1-covariance)

Deterministic identities used to transfer the LQG measure and the LQG metric to the dilated field
`h̃ = h(r ·) - h_r(0)` (ruling section 3, eqs. (7)-(9)), with `r = 1/2`:

* `normDilatePairing_eq_addFunPairing`: the normalized dilated pairing `normDilatePairing` of `S11s.lean` is the
  affine pullback pairing `affinePullbackPairing` (Defs/LQGMetric.lean) plus the constant `-s` (`addFunPairing`).
* `circleAverage_log_norm_smul`, `circleAverage_log_norm_zero`: scaling of the circle averages of `log‖·‖`,
  from Jensen's formula in Mathlib (`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`).
* `fieldCircleAverage_affinePullback`: at every positive radius, the circle averages of the affine pullback field
  are the dilated circle averages of `h = h^ℂ - α log|·|` (`dilatedCircleAverage`, FirstPass/S11q.lean).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set

/-- The normalized dilated pairing is the affine pullback pairing with the constant `-s`. -/
theorem normDilatePairing_eq_addFunPairing (T : (ℂ → ℝ) → ℝ) (s r : ℝ) :
    normDilatePairing T s r = addFunPairing (affinePullbackPairing T r 0) (fun _ => -s) := by
  funext φ
  have hn : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [normDilatePairing, addFunPairing, affinePullbackPairing, hn, neg_mul, integral_neg,
    integral_const_mul]
  ring

/-- Scaling of the circle average of `log‖·‖` (Jensen): for `r > 0` and `ρ ≠ 0`. -/
theorem circleAverage_log_norm_smul {r : ℝ} (hr : 0 < r) (z : ℂ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    Real.circleAverage (fun x : ℂ => Real.log ‖x‖) ((r : ℂ) * z) (r * ρ)
      = Real.log r + Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ρ := by
  have h1 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := (r : ℂ) * z)
    (mul_ne_zero hr.ne' hρ)
  have h2 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z) hρ
  simp only [sub_zero] at h1 h2
  have hz : (r * ρ)⁻¹ * ‖(r : ℂ) * z‖ = ρ⁻¹ * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    field_simp
  rw [h1, h2, Real.log_mul hr.ne' hρ, hz]
  ring

/-- `circleAverage (log‖·‖) 0 r = log r` for `r ≠ 0` (Jensen). -/
theorem circleAverage_log_norm_zero {r : ℝ} (hr : r ≠ 0) :
    Real.circleAverage (fun x : ℂ => Real.log ‖x‖) 0 r = Real.log r := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := 0) hr
  simp only [sub_zero, norm_zero, mul_zero, Real.posLog_zero, add_zero] at h
  exact h

/-- At every positive radius `ρ` (hence on the dyadic scales used by `IsLQGLimit`), the circle averages of the
affine pullback field `h̃_ρ(z) = h_{rρ}(rz) - h_r(0)` are the dilated circle averages of `h`:
`h̃_ρ(z) = h_{rρ}(rz) - h_r(0)` and `(α log)`-terms agree by Jensen's formula, with `h_r(0) = h^ℂ_r(0) - α log r`. -/
theorem fieldCircleAverage_affinePullback (α : ℝ) (hcirc : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r)
    {ρ : ℝ} (hρ : ρ ≠ 0) (z : ℂ) :
    fieldCircleAverage α (fun ρ' z' => hcirc (r * ρ') ((r : ℂ) * z') - hcirc r 0) ρ z
      = dilatedCircleAverage (fieldCircleAverage α hcirc) r ρ z := by
  simp only [fieldCircleAverage, dilatedCircleAverage]
  rw [circleAverage_log_norm_smul hr z hρ, circleAverage_log_norm_zero hr.ne']
  ring

end HarmonicBalls
