import HarmonicBalls.Proofs.Sec9.AffinePairingCovariance
import HarmonicBalls.Proofs.Sec8.LogarithmicPotential

/-! # Decay of mixed pairing covariances under dilation

The Section 8 imports use Leonardo Bonanno's LatticeProb formalization of the
 ergodic theorem. -/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- A continuous potential sampled at dyadically contracted points converges
in the integral against a compactly supported continuous density. -/
theorem tendsto_integral_mul_dyadic_comp {ψ u : ℂ → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hu : Continuous u) :
    Tendsto (fun n : ℕ => ∫ y, ψ y * u (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ) * y))
      atTop (𝓝 ((∫ y, ψ y) * u 0)) := by
  obtain ⟨R, hR⟩ := hψc.isBounded.subset_closedBall (0 : ℂ)
  let S := max R 0
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) S).exists_bound_of_continuousOn hu.continuousOn
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun y : ℂ => ψ y * u (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ) * y)) volume := by
    exact (hψ.mul (hu.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ y : ℂ ∂volume,
      ‖ψ y * u (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ) * y)‖ ≤ B * ‖ψ y‖ := by
    filter_upwards with y
    by_cases hy : ψ y = 0
    · simp [hy]
    · have hy' : y ∈ tsupport ψ := subset_tsupport ψ (by simpa using hy)
      have hyr : ‖y‖ ≤ S := by
        have h := hR hy'
        simp only [mem_closedBall, dist_zero_right] at h
        exact h.trans (le_max_left _ _)
      have hq : ‖((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_one₀ (by norm_num) (by norm_num)
      have hyS : (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ) * y) ∈ closedBall (0 : ℂ) S := by
        simp only [mem_closedBall, dist_zero_right, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg y) hq).trans hyr
      have huB : ‖u (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ) * y)‖ ≤ B :=
        (hC _ hyS).trans (le_max_left _ _)
      rw [norm_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left huB (norm_nonneg _)
  have hlim : ∀ᵐ y : ℂ ∂volume, Tendsto
      (fun n : ℕ => ψ y * u (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ) * y)) atTop (𝓝 (ψ y * u 0)) := by
    filter_upwards with y
    have hc : Tendsto (fun n : ℕ => (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ) * y)) atTop (𝓝 0) := by
      simpa using (Complex.continuous_ofReal.tendsto 0).comp hpow |>.mul_const y
    exact tendsto_const_nhds.mul ((hu.tendsto 0).comp hc)
  have ht := tendsto_integral_of_dominated_convergence (fun y => B * ‖ψ y‖)
    hm (hψi.norm.const_mul B) hb hlim
  simpa only [integral_mul_const] using ht

/-- The mixed covariance of the normalized dilation is an integral of the
original covariance potential over the contracted test function. -/
theorem IsWholePlaneGFF.covariance_affinePairing_eq_potential
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ)
    (hψzero : ∫ y, ψ y = 0) {a : ℂ} (ha : a ≠ 0) :
    cov[fun ω => hC ω φ, fun ω => affinePairing hC hcirc a 0 ω ψ; P] =
      ∫ y, ψ y * (∫ x, φ x * wholePlaneCov (a * y) x) := by
  have hψa := hψ.comp_inverse_complex_affine ha 0
  have hc := h.covariance_eq (.pairing (fun y => ψ ((y - 0) / a))) (.pairing φ) hψa hφ
  simp only [GFFObservable.eval] at hc
  have hn : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have he : (fun ω => affinePairing hC hcirc a 0 ω ψ) =
      (fun ω => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => ψ ((y - 0) / a))) := by
    funext ω
    simp [affinePairing, hψzero]
  rw [he, covariance_const_mul_right, covariance_comm, hc]
  change (‖a‖ ^ 2)⁻¹ * (∫ y, ψ ((y - 0) / a) *
    (∫ x, φ x * wholePlaneCov y x)) = _
  rw [integral_inverse_complex_affine_mul ψ _ ha 0]
  simp only [add_zero, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- For mean-zero tests the two whole-plane normalization terms cancel;
the remaining covariance is the logarithmic potential at the contracted test. -/
theorem IsWholePlaneGFF.covariance_affinePairing_eq_logPotential
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ)
    (hφzero : ∫ x, φ x = 0) (hψzero : ∫ y, ψ y = 0)
    {a : ℂ} (ha : a ≠ 0) :
    cov[fun ω => hC ω φ, fun ω => affinePairing hC hcirc a 0 ω ψ; P] =
      -(2 * Real.pi) * ∫ y, ψ y * planarLogPotential φ (a * y) := by
  have hψi : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hui : Integrable (fun y => ψ y * planarLogPotential φ (a * y)) :=
    (hψ.1.continuous.mul ((contDiff_planarLogPotential hφ).continuous.comp
      (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport hψ.2.1.mul_right
  rw [h.covariance_affinePairing_eq_potential hφ hψ hψzero ha]
  simp_rw [integral_mul_wholePlaneCov_of_integral_zero hφ.1.continuous hφ.2.1 hφzero]
  have heq : (fun y => ψ y * ((∫ x, φ x * wholePlaneNormalization x) -
      2 * Real.pi * planarLogPotential φ (a * y))) =
      (fun y => ψ y * (∫ x, φ x * wholePlaneNormalization x) -
        (2 * Real.pi) * (ψ y * planarLogPotential φ (a * y))) := by
    funext y
    ring
  rw [heq, integral_sub (hψi.mul_const _) (hui.const_mul _),
    integral_mul_const, hψzero, zero_mul, integral_const_mul]
  ring

/-- Mixed covariance of a GFF test pairing and a normalized dyadically
contracted mean-zero pairing tends to zero. -/
theorem IsWholePlaneGFF.tendsto_covariance_affinePairing_dyadic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ)
    (hψzero : ∫ y, ψ y = 0) :
    Tendsto (fun n : ℕ => cov[fun ω => hC ω φ,
      fun ω => affinePairing hC hcirc (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω ψ; P])
      atTop (𝓝 0) := by
  have hp : Continuous (fun z => ∫ x, φ x * wholePlaneCov z x) :=
    continuous_wholePlaneCov_potential_of_compact_support hφ.1.continuous hφ.2.1
  have ht := tendsto_integral_mul_dyadic_comp hψ.1.continuous hψ.2.1 hp
  simp only [hψzero, zero_mul] at ht
  apply ht.congr'
  filter_upwards with n
  symm
  exact h.covariance_affinePairing_eq_potential hφ hψ hψzero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity)))

#print axioms tendsto_integral_mul_dyadic_comp
#print axioms IsWholePlaneGFF.covariance_affinePairing_eq_potential
#print axioms IsWholePlaneGFF.covariance_affinePairing_eq_logPotential
#print axioms IsWholePlaneGFF.tendsto_covariance_affinePairing_dyadic
end HarmonicBalls
