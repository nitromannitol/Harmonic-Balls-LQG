import HarmonicBalls.FirstPass.Phase2.DomainMarkovCaccioppoli

/-!
# Bounds for the constant of the dual element

Write `avg f := avg_{∂B(0,1)} f` for the unit-circle average. The constant of the dual element of `v` with respect to a
cutoff `χ` is `c = avg (χ v) / (1 - avg χ)` (and `c = 0` when `avg χ = 1`). By Jensen's inequality for the circle
average, `c ^ 2 ≤ (1 - avg χ)⁻² avg ((χ v) ^ 2)`. Combined with the Caccioppoli identity for the variance of the
Laplacian pairing of the dual element, this bounds that variance by
`π⁻¹ ∫ |∇χ|² (v ^ 2 + c ^ 2)`.

## Main results

* `sq_circleAverage_le_circleAverage_sq`: Jensen's inequality `(avg_{∂B(c,R)} f) ^ 2 ≤ avg_{∂B(c,R)} f ^ 2`;
* `dualConstant_sq_le`: `dualConstant χ v ^ 2 ≤ (1 - avg χ)⁻² avg ((χ v) ^ 2)`;
* `integrable_gradientEnergy_mul`: `|∇χ|² w` is integrable for compactly supported `C¹` `χ` and continuous `w`;
* `wholePlaneGFFCov_laplacian_dualElement_self_le`: the variance bound above.
-/

open MeasureTheory Set Laplacian

namespace HarmonicBalls

/-- Jensen's inequality for circle averages of continuous functions: `(avg f) ^ 2 ≤ avg (f ^ 2)`. -/
theorem sq_circleAverage_le_circleAverage_sq {f : ℂ → ℝ} (hf : Continuous f) (c : ℂ) (R : ℝ) :
    Real.circleAverage f c R ^ 2 ≤ Real.circleAverage (fun x => f x ^ 2) c R := by
  set a := Real.circleAverage f c R with ha
  have hi : ∀ g : ℂ → ℝ, Continuous g → CircleIntegrable g c R :=
    fun g hg => hg.continuousOn.circleIntegrable'
  have h0 : 0 ≤ Real.circleAverage (fun x => (f x - a) ^ 2) c R :=
    Real.circleAverage_nonneg_of_nonneg fun x _ => sq_nonneg _
  have hexp : (fun x => (f x - a) ^ 2) = fun x => (f x ^ 2 - (2 * a) • f x) + a ^ 2 := by
    funext x
    simp only [smul_eq_mul]
    ring
  rw [hexp, Real.circleAverage_fun_add (hi (fun x => f x ^ 2 - (2 * a) • f x) (by fun_prop))
      (hi _ continuous_const),
    Real.circleAverage_fun_sub (hi (fun x => f x ^ 2) (by fun_prop)) (hi (fun x => (2 * a) • f x) (by fun_prop)),
    Real.circleAverage_fun_smul, Real.circleAverage_const, ← ha] at h0
  simp only [smul_eq_mul] at h0
  nlinarith [h0]

/-- The constant of the dual element is controlled by the unit-circle average of `(χ v) ^ 2`:
`dualConstant χ v ^ 2 ≤ (1 - avg_{∂B(0,1)} χ)⁻² avg_{∂B(0,1)} (χ v) ^ 2` (both sides vanish when the average of `χ`
is `1`). -/
theorem dualConstant_sq_le {χ v : ℂ → ℝ} (hχ : Continuous χ) (hv : Continuous v) :
    dualConstant χ v ^ 2 ≤
      ((1 - Real.circleAverage χ 0 1)⁻¹) ^ 2 * Real.circleAverage (fun x => (χ x * v x) ^ 2) 0 1 := by
  unfold dualConstant
  split_ifs with h
  · rw [h, sub_self, inv_zero]
    simp
  · rw [div_eq_inv_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (sq_circleAverage_le_circleAverage_sq (hχ.mul hv) 0 1) (sq_nonneg _)

/-- The gradient energy density `|∇χ|²` of a compactly supported `C¹` function, multiplied by a continuous function,
is integrable. -/
theorem integrable_gradientEnergy_mul {χ w : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hw : Continuous w) :
    Integrable (fun x => ((fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2) * w x) := by
  have hDc : HasCompactSupport (fderiv ℝ χ) := hχc.fderiv ℝ
  have hχd : ∀ u : ℂ, Continuous (fun x => fderiv ℝ χ x u) := fun u =>
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine Continuous.integrable_of_hasCompactSupport
    ((((hχd 1).pow 2).add ((hχd Complex.I).pow 2)).mul hw) (hDc.mono ?_)
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h0
  apply hx
  simp [h0]

/-- Variance bound for the Laplacian pairing of the dual element: if `χ` vanishes on the support of the mean-zero
test function `ρ`, then `G(Δφ, Δφ) ≤ π⁻¹ ∫ |∇χ|² ((outerPotential ρ) ^ 2 + c ^ 2)` for
`φ = dualElement χ (outerPotential ρ) c`. -/
theorem wholePlaneGFFCov_laplacian_dualElement_self_le {ρ χ : ℂ → ℝ} (hρ : IsTestFunction univ ρ)
    (h0 : ∫ y, ρ y = 0) (hχ : IsTestFunction univ χ) (hdisj : ∀ x, χ x ≠ 0 → ρ x = 0) (c : ℝ) :
    wholePlaneGFFCov (.pairing (Δ (dualElement χ (outerPotential ρ) c)))
        (.pairing (Δ (dualElement χ (outerPotential ρ) c))) ≤
      Real.pi⁻¹ *
        ∫ x, ((fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2) * (outerPotential ρ x ^ 2 + c ^ 2) := by
  rw [wholePlaneGFFCov_laplacian_dualElement_self hρ h0 hχ hdisj c]
  have hv : Continuous (outerPotential ρ) := (contDiff_outerPotential_of_integral_eq_zero hρ h0).continuous
  have hχ1 : ContDiff ℝ 1 χ := hχ.1.of_le (by simp)
  have hle : ∫ x, ((fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2) * (outerPotential ρ x + c) ^ 2 ≤
      ∫ x, ((fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2) *
        (2 * (outerPotential ρ x ^ 2 + c ^ 2)) := by
    refine integral_mono (integrable_gradientEnergy_mul hχ1 hχ.2.1 (by fun_prop))
      (integrable_gradientEnergy_mul hχ1 hχ.2.1 (by fun_prop)) fun x => ?_
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (outerPotential ρ x - c)]) (by positivity)
  have h2 : ∫ x, ((fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2) *
        (2 * (outerPotential ρ x ^ 2 + c ^ 2)) =
      2 * ∫ x, ((fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2) * (outerPotential ρ x ^ 2 + c ^ 2) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [h2] at hle
  have hπ : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  refine (mul_le_mul_of_nonneg_left hle hπ).trans_eq ?_
  ring

end HarmonicBalls
