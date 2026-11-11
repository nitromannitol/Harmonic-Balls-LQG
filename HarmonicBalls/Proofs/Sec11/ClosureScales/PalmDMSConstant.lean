import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec8.CircleLogPotential
import HarmonicBalls.Proposed.DuplantierMillerSheffield

/-! # Route (A), Step M: the constant term of the DMS shifted pairing vanishes on the closed unit disk

For `‖z‖ ≤ 1` the constant `dmsConstant γ z h₁₀ = -(h₁₀ + circleAverage (dmsShift γ z) 0 1)` vanishes as soon as the
unit-circle average `h₁₀ = hcirc · 1 0` of the whole-plane GFF vanishes, which holds almost surely
(`IsWholePlaneGFF.ae_circleAverage_one_zero`). The unit-circle average of `dmsShift γ z` is `-γ log max(1, |z|) = 0`:
on the unit circle the normalisation `γ log max(|w|, 1)` vanishes, and Jensen's formula gives the average of
`log|w - z|`. Hence, almost surely, the DMS shifted pairing is the field plus the deterministic shift
`∫ dmsShift_z φ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric

namespace HarmonicBalls

/-- The unit-circle average of the DMS shift `w ↦ -γ log|w - z| + γ log max(|w|, 1)` vanishes for `|z| ≤ 1`. -/
theorem circleAverage_dmsShift_unit (γ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Real.circleAverage (dmsShift γ z) 0 1 = 0 := by
  have h1 : Real.circleAverage (dmsShift γ z) 0 1 =
      Real.circleAverage (fun x => (-γ) • Real.log ‖x - z‖) 0 1 := by
    refine Real.circleAverage_congr_sphere ?_
    intro x hx
    have hx1 : ‖x‖ = 1 := by
      have h := mem_sphere.1 hx
      rw [dist_zero_right, abs_one] at h
      exact h
    simp only [dmsShift, hx1, max_self, Real.log_one, mul_zero, add_zero, smul_eq_mul]
  have h2 : Real.circleAverage (fun x => (-γ) • Real.log ‖x - z‖) 0 1 =
      (-γ) • Real.circleAverage (fun x => Real.log ‖x - z‖) 0 1 :=
    Real.circleAverage_fun_smul
  have hmax : max (1 : ℝ) ‖(0 : ℂ) - z‖ = 1 := by
    rw [zero_sub, norm_neg]
    exact max_eq_left hz
  rw [h1, h2, circleAverage_log_norm_sub_eq_log_max one_pos 0 z, hmax, Real.log_one, smul_zero]

/-- The constant term `dmsConstant γ z (hcirc · 1 0)` vanishes almost surely, for every `z` in the closed unit disk. -/
theorem dmsConstant_ae_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ∀ᵐ ω ∂P, dmsConstant γ z (hcirc ω 1 0) = 0 := by
  filter_upwards [hG.ae_circleAverage_one_zero] with ω hω
  simp only [dmsConstant, hω, circleAverage_dmsShift_unit γ hz, add_zero, neg_zero]

/-- Almost surely the DMS shifted pairing of the whole-plane field is the field plus the deterministic shift
`φ ↦ ∫ dmsShift_z φ`, for every `z` in the closed unit disk. -/
theorem dmsShiftedPairing_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ∀ᵐ ω ∂P, dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) =
      fun φ => hC ω φ + ∫ w, dmsShift γ z w * φ w := by
  filter_upwards [dmsConstant_ae_zero hG γ hz] with ω hω
  funext φ
  simp only [dmsShiftedPairing, hω, zero_mul, add_zero]

end HarmonicBalls

end
