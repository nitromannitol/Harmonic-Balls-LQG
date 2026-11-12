import HarmonicBalls.FirstPass.Phase2.DomainMarkovLaplacianPotential

/-!
# Dual element of a covariance potential

Let `χ` be a smooth compactly supported cutoff with `0 ≤ χ ≤ 1`, let `v` be a smooth function (in the application,
the covariance potential `outerPotential ρ` of a mean-zero test function `ρ` supported away from `tsupport χ`), and
let `c` be a real constant with `c (1 - avg_{∂B(0,1)} χ) = avg_{∂B(0,1)} (χ v)`. The *dual element*
`φ = -(2π)⁻¹ χ (v + c)` is a test function, and for the whole-plane GFF `h`

`Cov((h, ψ), (h, Δφ)) = ∫ ψ (χ (v + c) - c)`

for every test function `ψ`. Hence `Cov((h, ψ), (h, Δφ)) = ∫ ψ v` when `χ = 1` on the support of `ψ`, and
`Cov((h, ψ), (h, Δφ)) = 0` when `χ = 0` on the support of `ψ` and `∫ ψ = 0`. A constant `c` with the required
property exists whenever `v` has zero unit-circle average (`dualConstant_mul_eq`): if `avg_{∂B(0,1)} χ = 1` then
`χ = 1` on the unit circle and `avg_{∂B(0,1)} (χ v) = avg_{∂B(0,1)} v = 0`.

## Main results

* `isTestFunction_dualElement`: the dual element is a test function on every open set carrying `tsupport χ`;
* `IsWholePlaneGFF.covariance_pairing_laplacian_dualElement`: the covariance formula above;
* `IsWholePlaneGFF.covariance_pairing_laplacian_dualElement_of_eq_one`: `= ∫ ψ v` where `χ = 1`;
* `IsWholePlaneGFF.covariance_pairing_laplacian_dualElement_of_eq_zero`: `= 0` for mean-zero `ψ` where `χ = 0`;
* `dualConstant_mul_eq`: the constant `dualConstant χ v` has the required property.
-/

open MeasureTheory ProbabilityTheory Set Laplacian
open scoped ContDiff

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The dual element `-(2π)⁻¹ χ (v + c)` of a function `v` with respect to a cutoff `χ` and a constant `c`. -/
noncomputable def dualElement (χ v : ℂ → ℝ) (c : ℝ) (x : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * (χ x * (v x + c))

/-- The constant `c` of the dual element: `avg_{∂B(0,1)} (χ v) / (1 - avg_{∂B(0,1)} χ)`, and `0` when
`avg_{∂B(0,1)} χ = 1`. -/
noncomputable def dualConstant (χ v : ℂ → ℝ) : ℝ :=
  if Real.circleAverage χ 0 1 = 1 then 0
  else Real.circleAverage (fun x => χ x * v x) 0 1 / (1 - Real.circleAverage χ 0 1)

theorem support_dualElement_subset (χ v : ℂ → ℝ) (c : ℝ) :
    Function.support (dualElement χ v c) ⊆ Function.support χ := by
  intro x hx h0
  exact hx (by simp [dualElement, show χ x = 0 from h0])

/-- **Test function.** For a test function `χ` on `U` and a smooth `v`, the dual element is a test function
on `U`. -/
theorem isTestFunction_dualElement {U : Set ℂ} {χ v : ℂ → ℝ} (hχ : IsTestFunction U χ)
    (hv : ContDiff ℝ ∞ v) (c : ℝ) : IsTestFunction U (dualElement χ v c) :=
  ⟨contDiff_const.mul (hχ.1.mul (hv.add contDiff_const)),
    hχ.2.1.mono (support_dualElement_subset χ v c),
    (closure_mono (support_dualElement_subset χ v c)).trans hχ.2.2⟩

/-- The unit-circle average of the dual element. -/
theorem circleAverage_dualElement {χ v : ℂ → ℝ} (hχ : Continuous χ) (hv : Continuous v) (c : ℝ) :
    Real.circleAverage (dualElement χ v c) 0 1 =
      -(2 * Real.pi)⁻¹ *
        (Real.circleAverage (fun x => χ x * v x) 0 1 + c * Real.circleAverage χ 0 1) := by
  have h1 : CircleIntegrable (fun x => χ x * v x) 0 1 := (hχ.mul hv).continuousOn.circleIntegrable'
  have h2 : CircleIntegrable (fun x => c • χ x) 0 1 :=
    (show Continuous (fun x => c • χ x) from hχ.const_smul c).continuousOn.circleIntegrable'
  have hfun : dualElement χ v c = fun x => (-(2 * Real.pi)⁻¹) • (χ x * v x + c • χ x) := by
    funext x
    simp only [dualElement, smul_eq_mul]
    ring
  rw [hfun, Real.circleAverage_fun_smul, Real.circleAverage_fun_add h1 h2, Real.circleAverage_fun_smul,
    smul_eq_mul, smul_eq_mul]

/-- **Covariance with the Laplacian of the dual element.** If `c (1 - avg_{∂B(0,1)} χ) = avg_{∂B(0,1)} (χ v)`,
then `Cov((h, ψ), (h, Δφ)) = ∫ ψ (χ (v + c) - c)` for the dual element `φ = -(2π)⁻¹ χ (v + c)` and every test
function `ψ`. -/
theorem IsWholePlaneGFF.covariance_pairing_laplacian_dualElement (hh : IsWholePlaneGFF P hC hcirc)
    {ψ χ v : ℂ → ℝ} {c : ℝ} (hψ : IsTestFunction univ ψ) (hχ : IsTestFunction univ χ)
    (hv : ContDiff ℝ ∞ v)
    (hc : c * (1 - Real.circleAverage χ 0 1) = Real.circleAverage (fun x => χ x * v x) 0 1) :
    cov[fun s => hC s ψ, fun s => hC s (Δ (dualElement χ v c)); P] =
      ∫ x, ψ x * (χ x * (v x + c) - c) := by
  have hφ := isTestFunction_dualElement hχ hv c
  rw [hh.covariance_pairing_laplacian_eq_integral hψ hφ.1 hφ.2.1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [circleAverage_dualElement hχ.1.continuous hv.continuous c]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  set L := Real.circleAverage (fun x => χ x * v x) 0 1
  set a := Real.circleAverage χ 0 1
  simp only [dualElement]
  linear_combination (ψ x * (χ x * (v x + c) - L - c * a)) * mul_inv_cancel₀ hπ + ψ x * hc

/-- **Inner covariance.** Where `χ = 1` on the support of `ψ`, `Cov((h, ψ), (h, Δφ)) = ∫ ψ v`. -/
theorem IsWholePlaneGFF.covariance_pairing_laplacian_dualElement_of_eq_one (hh : IsWholePlaneGFF P hC hcirc)
    {ψ χ v : ℂ → ℝ} {c : ℝ} (hψ : IsTestFunction univ ψ) (hχ : IsTestFunction univ χ)
    (hv : ContDiff ℝ ∞ v)
    (hc : c * (1 - Real.circleAverage χ 0 1) = Real.circleAverage (fun x => χ x * v x) 0 1)
    (hψχ : ∀ x, ψ x ≠ 0 → χ x = 1) :
    cov[fun s => hC s ψ, fun s => hC s (Δ (dualElement χ v c)); P] = ∫ x, ψ x * v x := by
  rw [hh.covariance_pairing_laplacian_dualElement hψ hχ hv hc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases h : ψ x = 0
  · simp [h]
  · simp only [hψχ x h]
    ring

/-- **Outer orthogonality.** Where `χ = 0` on the support of a mean-zero `ψ`, `Cov((h, ψ), (h, Δφ)) = 0`. -/
theorem IsWholePlaneGFF.covariance_pairing_laplacian_dualElement_of_eq_zero (hh : IsWholePlaneGFF P hC hcirc)
    {ψ χ v : ℂ → ℝ} {c : ℝ} (hψ : IsTestFunction univ ψ) (hχ : IsTestFunction univ χ)
    (hv : ContDiff ℝ ∞ v)
    (hc : c * (1 - Real.circleAverage χ 0 1) = Real.circleAverage (fun x => χ x * v x) 0 1)
    (hψχ : ∀ x, ψ x ≠ 0 → χ x = 0) (hψ0 : ∫ x, ψ x = 0) :
    cov[fun s => hC s ψ, fun s => hC s (Δ (dualElement χ v c)); P] = 0 := by
  rw [hh.covariance_pairing_laplacian_dualElement hψ hχ hv hc]
  have hpt : ∀ x, ψ x * (χ x * (v x + c) - c) = -c * ψ x := by
    intro x
    by_cases h : ψ x = 0
    · simp [h]
    · simp only [hψχ x h]
      ring
  simp only [hpt, integral_const_mul, hψ0, mul_zero]

/-- **The constant of the dual element.** For a continuous cutoff `χ ≤ 1` and a continuous `v` with zero
unit-circle average, `dualConstant χ v (1 - avg_{∂B(0,1)} χ) = avg_{∂B(0,1)} (χ v)`. When
`avg_{∂B(0,1)} χ = 1`, the bound `|avg (χ v) - avg v| ≤ M avg (1 - χ) = 0` (with `|v| ≤ M` on the unit
circle) gives `avg (χ v) = 0`. -/
theorem dualConstant_mul_eq {χ v : ℂ → ℝ} (hχ : Continuous χ) (hχ1 : ∀ x, χ x ≤ 1) (hv : Continuous v)
    (hv0 : Real.circleAverage v 0 1 = 0) :
    dualConstant χ v * (1 - Real.circleAverage χ 0 1) = Real.circleAverage (fun x => χ x * v x) 0 1 := by
  unfold dualConstant
  split_ifs with h
  · rw [zero_mul]
    obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) |1|).exists_bound_of_continuousOn hv.continuousOn
    have h1 : CircleIntegrable (fun x => χ x * v x) 0 1 := (hχ.mul hv).continuousOn.circleIntegrable'
    have hv' : CircleIntegrable v 0 1 := hv.continuousOn.circleIntegrable'
    have hdiff : Real.circleAverage (fun x => χ x * v x) 0 1 - Real.circleAverage v 0 1 =
        Real.circleAverage (fun x => (χ x - 1) * v x) 0 1 := by
      rw [← Real.circleAverage_fun_sub h1 hv']
      congr 1
      funext x
      ring
    have hχc : CircleIntegrable (fun x => M • (1 - χ x)) 0 1 :=
      (show Continuous (fun x => M • (1 - χ x)) from
        (continuous_const.sub hχ).const_smul M).continuousOn.circleIntegrable'
    have habs : CircleIntegrable |fun x => (χ x - 1) * v x| 0 1 :=
      ((hχ.sub continuous_const).mul hv).abs.continuousOn.circleIntegrable'
    have h1c : CircleIntegrable (fun _ : ℂ => (1 : ℝ)) 0 1 := continuous_const.continuousOn.circleIntegrable'
    have hχi : CircleIntegrable χ 0 1 := hχ.continuousOn.circleIntegrable'
    have hbound : |Real.circleAverage (fun x => (χ x - 1) * v x) 0 1| ≤ 0 := by
      calc _ ≤ Real.circleAverage |fun x => (χ x - 1) * v x| 0 1 :=
            Real.abs_circleAverage_le_circleAverage_abs
        _ ≤ Real.circleAverage (fun x => M • (1 - χ x)) 0 1 := by
            refine Real.circleAverage_mono habs hχc fun x hx => ?_
            have hMx := hM x hx
            rw [Real.norm_eq_abs] at hMx
            simp only [Pi.abs_apply, abs_mul, smul_eq_mul]
            rw [abs_of_nonpos (show χ x - 1 ≤ 0 by linarith [hχ1 x])]
            nlinarith [mul_le_mul_of_nonneg_left hMx (show 0 ≤ 1 - χ x by linarith [hχ1 x])]
        _ = 0 := by
            rw [Real.circleAverage_fun_smul, Real.circleAverage_fun_sub h1c hχi, Real.circleAverage_const,
              h, sub_self, smul_zero]
    have h0 := abs_nonpos_iff.mp hbound
    linarith
  · exact div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm h))

end HarmonicBalls
