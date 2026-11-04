import HarmonicBalls.Proofs.Sec8.LaplacianCovarianceEnergy
import HarmonicBalls.Proofs.Sec6.LaplacianConvolution

/-! # Planar logarithmic potential of a test function

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem. -/

open MeasureTheory ProbabilityTheory Metric Set Laplacian Filter
open scoped Topology ProbabilityTheory Convolution ContDiff

namespace HarmonicBalls

/-- The logarithmic fundamental solution integrated against a planar test
function, normalized so that its Laplacian is the test function. -/
noncomputable def planarLogPotential (φ : ℂ → ℝ) : ℂ → ℝ :=
  ((2 * Real.pi)⁻¹ : ℝ) •
    (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x : ℂ => Real.log ‖x‖)

/-- The logarithmic kernel is locally integrable on the complex plane. -/
theorem locallyIntegrable_log_norm_complex :
    LocallyIntegrable (fun x : ℂ => Real.log ‖x‖) volume := by
  simpa using (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm (0 : ℂ))

/-- Convolution with a test function makes its logarithmic potential smooth. -/
theorem contDiff_planarLogPotential {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    ContDiff ℝ ∞ (planarLogPotential φ) := by
  unfold planarLogPotential
  exact contDiff_const.smul
    (hφ.2.1.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hφ.1 locallyIntegrable_log_norm_complex)

/-- The planar logarithmic potential solves the Poisson equation for every
smooth compactly supported source. -/
theorem laplacian_planarLogPotential {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Δ (planarLogPotential φ) = φ := by
  let F : ℂ → ℝ := φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    fun x : ℂ => Real.log ‖x‖
  have hF : ContDiff ℝ ∞ F := hφ.2.1.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hφ.1 locallyIntegrable_log_norm_complex
  have hΔ : Δ F = (Δ φ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun x : ℂ => Real.log ‖x‖ :=
    Section6.laplacian_convolution_left hφ.1 hφ.2.1 locallyIntegrable_log_norm_complex
  funext x
  change Δ (((2 * Real.pi)⁻¹ : ℝ) • F) x = φ x
  rw [InnerProductSpace.laplacian_smul _ (hF.contDiffAt.of_le (by norm_num)), hΔ]
  rw [MeasureTheory.convolution_def]
  change (2 * Real.pi)⁻¹ * (∫ y, Δ φ y * Real.log ‖x - y‖) = φ x
  have hfund : (∫ y, Δ φ y * Real.log ‖x - y‖) = 2 * Real.pi * φ x := by
    simpa only [mul_comm, norm_sub_rev] using
      integral_log_norm_sub_mul_laplacian (hφ.1.of_le (by norm_num)) hφ.2.1 x
  rw [hfund]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  field_simp

/-- The logarithmic potential as an ordinary integral. -/
theorem planarLogPotential_eq_integral (φ : ℂ → ℝ) (x : ℂ) :
    planarLogPotential φ x =
      (2 * Real.pi)⁻¹ * ∫ y, φ y * Real.log ‖y - x‖ := by
  unfold planarLogPotential
  rw [Pi.smul_apply, MeasureTheory.convolution_def]
  change (2 * Real.pi)⁻¹ * (∫ y, φ y * Real.log ‖x - y‖) = _
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [norm_sub_rev]

/-- The whole-plane covariance potential of a mean-zero test function is its
normalization constant minus its logarithmic potential. -/
theorem integral_mul_wholePlaneCov_of_integral_zero {φ : ℂ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφzero : ∫ y, φ y = 0)
    (x : ℂ) :
    (∫ y, φ y * wholePlaneCov x y) =
      (∫ y, φ y * wholePlaneNormalization y) - 2 * Real.pi * planarLogPotential φ x := by
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hni : Integrable (fun y => φ y * wholePlaneNormalization y) :=
    (hφ.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hφc.mul_right
  have hli : Integrable (fun y => φ y * Real.log ‖y - x‖) := by
    have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
      ).integrable_smul_right_of_hasCompactSupport hφ hφc
    simpa only [smul_eq_mul, mul_comm] using h
  have heq : (∫ y, φ y * wholePlaneCov x y) =
      ∫ y, (φ y * wholePlaneNormalization x + φ y * wholePlaneNormalization y) -
        φ y * Real.log ‖y - x‖ := by
    apply integral_congr_ae
    filter_upwards [ae_ne_complex x] with y hy
    have hxy : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.symm)
    have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    have hy' : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    rw [wholePlaneCov, Real.log_div (mul_ne_zero hx hy') hxy, Real.log_mul hx hy', norm_sub_rev]
    simp only [wholePlaneNormalization]
    ring
  have hai : Integrable (fun y => φ y * wholePlaneNormalization x +
      φ y * wholePlaneNormalization y) := (hφi.mul_const _).add hni
  have hp : 2 * Real.pi * planarLogPotential φ x =
      ∫ y, φ y * Real.log ‖y - x‖ := by
    rw [planarLogPotential_eq_integral, ← mul_assoc,
      mul_inv_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero), one_mul]
  rw [heq, integral_sub hai hli, integral_add (hφi.mul_const _) hni,
    integral_mul_const, hφzero, zero_mul, zero_add, hp]

/-- The covariance energy of a mean-zero test function is its pairing with
the logarithmic potential. -/
theorem wholePlaneGFFCov_pairing_self_eq_logPotential {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hφzero : ∫ x, φ x = 0) :
    wholePlaneGFFCov (.pairing φ) (.pairing φ) =
      -2 * Real.pi * ∫ x, φ x * planarLogPotential φ x := by
  have hφi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hφui : Integrable (fun x => φ x * planarLogPotential φ x) :=
    (hφ.1.continuous.mul (contDiff_planarLogPotential hφ).continuous
      ).integrable_of_hasCompactSupport hφ.2.1.mul_right
  let a : ℝ := ∫ y, φ y * wholePlaneNormalization y
  change (∫ x, φ x * (∫ y, φ y * wholePlaneCov x y)) = _
  simp_rw [integral_mul_wholePlaneCov_of_integral_zero hφ.1.continuous hφ.2.1 hφzero]
  change (∫ x, φ x * (a - 2 * Real.pi * planarLogPotential φ x)) = _
  calc
    _ = ∫ x, φ x * a - (2 * Real.pi) * (φ x * planarLogPotential φ x) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (∫ x, φ x) * a - (2 * Real.pi) *
        ∫ x, φ x * planarLogPotential φ x := by
      rw [integral_sub (hφi.mul_const a) (hφui.const_mul _), integral_mul_const, integral_const_mul]
    _ = _ := by rw [hφzero]; ring

/-- The error for a compact potential can be expressed against the canonical
logarithmic potential of the test function. -/
theorem IsWholePlaneGFF.laplacian_covariance_error_eq_logPotential
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hφzero : ∫ x, φ x = 0)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hΔψ : IsTestFunction univ (Δ ψ)) :
    wholePlaneGFFCov (.pairing (Δ ψ)) (.pairing (Δ ψ)) +
      wholePlaneGFFCov (.pairing φ) (.pairing φ) -
      2 * wholePlaneGFFCov (.pairing (Δ ψ)) (.pairing φ) =
      -2 * Real.pi * (∫ x, φ x * planarLogPotential φ x) -
      2 * Real.pi * (∫ x, Δ ψ x * ψ x) +
      4 * Real.pi * ∫ x, φ x * ψ x := by
  rw [h.laplacian_covariance_error_eq_integrals hφ hφzero hψ hψc hΔψ,
    wholePlaneGFFCov_pairing_self_eq_logPotential hφ hφzero]

end HarmonicBalls
