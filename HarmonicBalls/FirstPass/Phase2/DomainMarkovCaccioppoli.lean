import HarmonicBalls.FirstPass.Phase2.DomainMarkovDualElement
import HarmonicBalls.Proofs.Sec8.LogarithmicPotential
import HarmonicBalls.Proofs.Sec8.LaplacianCovarianceEnergy

/-!
# Caccioppoli identity for the dual element

For a mean-zero test function `ρ`, the covariance potential `v = outerPotential ρ` is `-2π` times the planar
logarithmic potential of `ρ` plus a constant, so `Δv = -2π ρ`; in particular `v` is harmonic off the support of
`ρ`. For a smooth compactly supported cutoff `χ` and a smooth `w` harmonic on `{χ ≠ 0}` the *Caccioppoli
identity* `∫ |∇(χ w)|² = ∫ |∇χ|² w²` holds (one integration by parts: `∫ ∇w · ∇(χ² w) = -∫ χ² w Δw = 0`).
Consequently the Laplacian pairing of the dual element `φ = -(2π)⁻¹ χ (v + c)` has covariance

`G((Δφ), (Δφ)) = (2π)⁻¹ ∫ |∇χ|² (v + c)²`

whenever `χ` vanishes on the support of `ρ`; only the values of `v` on `tsupport χ` enter.

## Main results

* `laplacian_outerPotential`: `Δ (outerPotential ρ) = -2π ρ` for a mean-zero test function `ρ`;
* `integral_dirichletEnergy_mul_of_laplacian_eq_zero`: the Caccioppoli identity;
* `wholePlaneGFFCov_laplacian_dualElement_self`: the covariance of the Laplacian pairing of the dual element.
-/

open MeasureTheory Set Laplacian
open scoped ContDiff

namespace HarmonicBalls

/-- For a mean-zero test function the covariance potential is `-2π` times the planar logarithmic potential plus
a constant. -/
theorem outerPotential_eq_planarLogPotential {ρ : ℂ → ℝ} (hρ : IsTestFunction univ ρ) (h0 : ∫ y, ρ y = 0) :
    outerPotential ρ = (-(2 * Real.pi)) • planarLogPotential ρ +
      fun _ => ∫ y, ρ y * LQGMetric.CircleAvg.circLog 0 1 y := by
  funext x
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  rw [outerPotential_eq_logPot_add_of_integral_eq_zero hρ h0]
  have hlog : LQGMetric.CircleAvg.logPot ρ x = -∫ t, ρ t * Real.log ‖x - t‖ := by
    rw [show LQGMetric.CircleAvg.logPot ρ x = ∫ y, -Real.log ‖x - y‖ * ρ y from rfl, ← integral_neg]
    congr 1
    funext t
    ring
  have hconv : planarLogPotential ρ x = (2 * Real.pi)⁻¹ * ∫ t, ρ t * Real.log ‖x - t‖ := by
    simp only [planarLogPotential, Pi.smul_apply, convolution_def, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hlog, hconv, neg_mul, mul_inv_cancel_left₀ hπ]

/-- The Laplacian of `f + c` is the Laplacian of `f`. -/
theorem laplacian_add_const {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : ℂ) :
    Δ (fun y => f y + c) x = Δ f x := by
  rw [laplacian_eq_fderiv_fderiv (hf.add contDiff_const), laplacian_eq_fderiv_fderiv hf]
  simp only [fderiv_add_const]

/-- **Poisson equation for the covariance potential.** For a mean-zero test function `ρ`,
`Δ (outerPotential ρ) = -2π ρ`; in particular the covariance potential is harmonic off the support of `ρ`. -/
theorem laplacian_outerPotential {ρ : ℂ → ℝ} (hρ : IsTestFunction univ ρ) (h0 : ∫ y, ρ y = 0) (x : ℂ) :
    Δ (outerPotential ρ) x = -(2 * Real.pi) * ρ x := by
  have hP : ContDiff ℝ 2 (planarLogPotential ρ) := (contDiff_planarLogPotential hρ).of_le (by simp)
  rw [outerPotential_eq_planarLogPotential hρ h0]
  change Δ (fun y => ((-(2 * Real.pi)) • planarLogPotential ρ) y +
    ∫ y, ρ y * LQGMetric.CircleAvg.circLog 0 1 y) x = _
  rw [laplacian_add_const (f := (-(2 * Real.pi)) • planarLogPotential ρ)
    (hP.const_smul (-(2 * Real.pi))), InnerProductSpace.laplacian_smul _ hP.contDiffAt, laplacian_planarLogPotential hρ,
    smul_eq_mul]

/-- **Caccioppoli identity.** For a smooth compactly supported `χ` and a smooth `w` with `Δw = 0` on `{χ ≠ 0}`,
`∫ |∇(χ w)|² = ∫ |∇χ|² w²` (gradients in the orthonormal directions `1` and `I`). -/
theorem integral_dirichletEnergy_mul_of_laplacian_eq_zero {χ w : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (hw : ContDiff ℝ 2 w) (hΔ : ∀ x, χ x ≠ 0 → Δ w x = 0) :
    ∫ x, (fderiv ℝ (fun y => χ y * w y) x 1) ^ 2 + (fderiv ℝ (fun y => χ y * w y) x Complex.I) ^ 2 =
      ∫ x, ((fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2) * w x ^ 2 := by
  obtain ⟨g, hg_def⟩ : ∃ g : ℂ → ℝ, g = fun y => χ y * (χ y * w y) := ⟨_, rfl⟩
  have hg : ContDiff ℝ 2 g := hg_def ▸ hχ.mul (hχ.mul hw)
  have hgc : HasCompactSupport g := hg_def ▸ hχc.mul_right
  -- pointwise algebra: `(∂(χ w))² = (∂χ)² w² + ∂(χ² w) ∂w`
  have hpt : ∀ (u x : ℂ), (fderiv ℝ (fun y => χ y * w y) x u) ^ 2 =
      (fderiv ℝ χ x u) ^ 2 * w x ^ 2 + fderiv ℝ g x u * fderiv ℝ w x u := by
    intro u x
    have hχd : DifferentiableAt ℝ χ x := hχ.differentiable (by norm_num) x
    have hwd : DifferentiableAt ℝ w x := hw.differentiable (by norm_num) x
    rw [hg_def, fderiv_fun_mul (d := fun y => χ y * w y) hχd (hχd.mul hwd), fderiv_fun_mul hχd hwd]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  -- one integration by parts in each direction
  have key : ∀ u : ℂ,
      Integrable (fun x => fderiv ℝ g x u * fderiv ℝ w x u) ∧
      Integrable (fun x => g x * fderiv ℝ (fun y => fderiv ℝ w y u) x u) ∧
      (∫ x, fderiv ℝ g x u * fderiv ℝ w x u) =
        -∫ x, g x * fderiv ℝ (fun y => fderiv ℝ w y u) x u := by
    intro u
    have hd : ContDiff ℝ 1 (fun x => fderiv ℝ w x u) :=
      (hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hgd : Continuous (fun x => fderiv ℝ g x u) :=
      (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hgdc : HasCompactSupport (fun x => fderiv ℝ g x u) :=
      (hgc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L u) (by simp)
    have hdd : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ w y u) x u) :=
      (hd.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have i1 : Integrable (fun x => fderiv ℝ g x u * fderiv ℝ w x u) :=
      (hgd.mul hd.continuous).integrable_of_hasCompactSupport hgdc.mul_right
    have i2 : Integrable (fun x => g x * fderiv ℝ (fun y => fderiv ℝ w y u) x u) :=
      (hg.continuous.mul hdd).integrable_of_hasCompactSupport hgc.mul_right
    have i3 : Integrable (fun x => g x * fderiv ℝ w x u) :=
      (hg.continuous.mul hd.continuous).integrable_of_hasCompactSupport hgc.mul_right
    refine ⟨i1, i2, ?_⟩
    rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
      (fun x _ => hg.differentiable (by norm_num) x) (fun x _ => hd.differentiable one_ne_zero x), neg_neg]
  obtain ⟨i1, i2, e1⟩ := key 1
  obtain ⟨j1, j2, e2⟩ := key Complex.I
  have hDc : HasCompactSupport (fderiv ℝ χ) := hχc.fderiv ℝ
  have hχd : ∀ u : ℂ, Continuous (fun x => fderiv ℝ χ x u) := fun u =>
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hE : Integrable (fun x => ((fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2) * w x ^ 2) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((((hχd 1).pow 2).add ((hχd Complex.I).pow 2)).mul (hw.continuous.pow 2)) (hDc.mono ?_)
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp [h0]
  have hsplit : (fun x => (fderiv ℝ (fun y => χ y * w y) x 1) ^ 2 +
      (fderiv ℝ (fun y => χ y * w y) x Complex.I) ^ 2) =
      fun x => ((fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2) * w x ^ 2 +
        (fderiv ℝ g x 1 * fderiv ℝ w x 1 + fderiv ℝ g x Complex.I * fderiv ℝ w x Complex.I) := by
    funext x
    rw [hpt 1 x, hpt Complex.I x]
    ring
  have hzero : ∀ x, g x * fderiv ℝ (fun y => fderiv ℝ w y 1) x 1 +
      g x * fderiv ℝ (fun y => fderiv ℝ w y Complex.I) x Complex.I = 0 := by
    intro x
    rw [← mul_add, ← laplacian_eq_fderiv_fderiv hw x, hg_def]
    by_cases h : χ x = 0
    · simp [h]
    · simp [hΔ x h]
  have ij : Integrable (fun x => fderiv ℝ g x 1 * fderiv ℝ w x 1 +
      fderiv ℝ g x Complex.I * fderiv ℝ w x Complex.I) := i1.add j1
  rw [hsplit, integral_add hE ij, integral_add i1 j1, e1, e2, ← neg_add, ← integral_add i2 j2]
  simp only [hzero, integral_zero, neg_zero, add_zero]

/-- **Covariance of the Laplacian pairing of the dual element.** For a mean-zero test function `ρ` and a test
function `χ` vanishing on the support of `ρ`, the dual element `φ = -(2π)⁻¹ χ (outerPotential ρ + c)` satisfies
`G((Δφ), (Δφ)) = (2π)⁻¹ ∫ |∇χ|² (outerPotential ρ + c)²`. -/
theorem wholePlaneGFFCov_laplacian_dualElement_self {ρ χ : ℂ → ℝ} (hρ : IsTestFunction univ ρ)
    (h0 : ∫ y, ρ y = 0) (hχ : IsTestFunction univ χ) (hdisj : ∀ x, χ x ≠ 0 → ρ x = 0) (c : ℝ) :
    wholePlaneGFFCov (.pairing (Δ (dualElement χ (outerPotential ρ) c)))
        (.pairing (Δ (dualElement χ (outerPotential ρ) c))) =
      (2 * Real.pi)⁻¹ *
        ∫ x, ((fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2) * (outerPotential ρ x + c) ^ 2 := by
  have hv := contDiff_outerPotential_of_integral_eq_zero hρ h0
  have hv2 : ContDiff ℝ 2 (outerPotential ρ) := hv.of_le (by simp)
  have hχ2 : ContDiff ℝ 2 χ := hχ.1.of_le (by simp)
  have hφ := isTestFunction_dualElement hχ hv c
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  rw [wholePlaneGFFCov_laplacian_self_eq_dirichlet_energy (hφ.1.of_le (by simp)) hφ.2.1]
  have hD : ∀ x u, fderiv ℝ (dualElement χ (outerPotential ρ) c) x u =
      -(2 * Real.pi)⁻¹ * fderiv ℝ (fun y => χ y * (outerPotential ρ y + c)) x u := by
    intro x u
    have hd : DifferentiableAt ℝ (fun y => χ y * (outerPotential ρ y + c)) x :=
      ((hχ2.mul (hv2.add contDiff_const)).differentiable (by norm_num)) x
    rw [show dualElement χ (outerPotential ρ) c =
      fun y => -(2 * Real.pi)⁻¹ * (χ y * (outerPotential ρ y + c)) from rfl, fderiv_const_mul hd]
    simp only [_root_.smul_apply, smul_eq_mul]
  have hΔ : ∀ x, χ x ≠ 0 → Δ (fun y => outerPotential ρ y + c) x = 0 := by
    intro x hx
    rw [laplacian_add_const hv2, laplacian_outerPotential hρ h0, hdisj x hx, mul_zero]
  have hsq : ∀ x, (fderiv ℝ (dualElement χ (outerPotential ρ) c) x 1) ^ 2 +
      (fderiv ℝ (dualElement χ (outerPotential ρ) c) x Complex.I) ^ 2 =
      ((2 * Real.pi)⁻¹) ^ 2 * ((fderiv ℝ (fun y => χ y * (outerPotential ρ y + c)) x 1) ^ 2 +
        (fderiv ℝ (fun y => χ y * (outerPotential ρ y + c)) x Complex.I) ^ 2) := by
    intro x
    rw [hD, hD]
    ring
  simp only [hsq]
  rw [integral_const_mul, integral_dirichletEnergy_mul_of_laplacian_eq_zero hχ2 hχ.2.1
    (hv2.add contDiff_const) hΔ]
  field_simp
