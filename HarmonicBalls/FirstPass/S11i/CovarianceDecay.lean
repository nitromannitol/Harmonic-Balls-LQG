import HarmonicBalls.FirstPass.S11i.LogPotentialFubini
import HarmonicBalls.Defs.GFF

/-!
# Step 8 helper: covariance decay of the dilated whole-plane GFF

Source: corrected paper, lemma `s11-pinch:lem:mixing` (tex lines 3769-3812). For test functions `f, k` with
`∫ k = 0`, the covariance of the pairing with `f` and the pairing with the dilated test function `κₙ k`
(`dilateTest n k`, the kernel of `(𝒯ⁿ h, k) = (h, κₙ k)`) is

  `Cov((h, f), (h, κₙ k)) = -∫ z, k z * G_f(2⁻ⁿ z) → -G_f(0) ∫ k = 0`,

where `G_f(w) = ∫ f x log ‖x - w‖ dx` is continuous (`continuous_logPotential`). The decay is for ALL test
functions `f` (no mean-zero condition on `f`: the constant part of `wholePlaneCov` integrates to zero against `k`).
-/

open MeasureTheory Filter Topology Metric Set

namespace HarmonicBalls

/-- `2⁻ⁿ → 0` as `n → ∞`. -/
theorem tendsto_inv_two_pow :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- `2⁻ⁿ ∈ [0, 1]`. -/
theorem inv_two_pow_mem_Icc (n : ℕ) : ((2 : ℝ) ^ n)⁻¹ ∈ Icc (0 : ℝ) 1 :=
  ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))⟩

/-- Dominated convergence for a continuous `G`: `∫ k z G(2⁻ⁿ z) dz → G(0) ∫ k = 0`. -/
theorem tendsto_integral_mul_comp_inv_two_pow (G : ℂ → ℝ) (hG : Continuous G) {k : ℂ → ℝ}
    (hk : IsTestFunction univ k) {R : ℝ} (hkR : ∀ z, k z ≠ 0 → ‖z‖ ≤ R) (hmean : ∫ z, k z = 0) :
    Tendsto (fun n : ℕ => ∫ z, k z * G (((2 : ℝ) ^ n)⁻¹ • z)) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hG.continuousOn
  have hkc : Continuous k := hk.1.continuous
  have hint : Integrable (fun z => ‖k z‖ * M) := (integrable_of_isTestFunction hk).norm.mul_const M
  have hbound : ∀ n : ℕ, ∀ z : ℂ, ‖k z * G (((2 : ℝ) ^ n)⁻¹ • z)‖ ≤ ‖k z‖ * M := by
    intro n z
    rw [norm_mul]
    by_cases hz : k z = 0
    · simp [hz]
    · have hcz : ‖((2 : ℝ) ^ n)⁻¹ • z‖ ≤ R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_two_pow_mem_Icc n).1]
        have := mul_le_mul_of_nonneg_right (inv_two_pow_mem_Icc n).2 (norm_nonneg z)
        linarith [hkR z hz]
      exact mul_le_mul_of_nonneg_left (hM _ (mem_closedBall_zero_iff.2 hcz)) (norm_nonneg _)
  have hpt : ∀ z : ℂ, Tendsto (fun n : ℕ => k z * G (((2 : ℝ) ^ n)⁻¹ • z)) atTop (𝓝 (k z * G 0)) := by
    intro z
    have hc : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ • z) atTop (𝓝 0) := by
      simpa using tendsto_inv_two_pow.smul_const z
    exact ((hG.tendsto 0).comp hc).const_mul (k z)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun z => k z * G (((2 : ℝ) ^ n)⁻¹ • z)) volume :=
    fun n => (hkc.mul (hG.comp (continuous_id.const_smul (((2 : ℝ) ^ n)⁻¹)))).aestronglyMeasurable
  have hlim := tendsto_integral_filter_of_dominated_convergence (fun z => ‖k z‖ * M)
    (Eventually.of_forall hmeas) (Eventually.of_forall fun n => ae_of_all _ (hbound n)) hint
    (ae_of_all _ hpt)
  have hval : ∫ z, k z * G 0 = 0 := by
    rw [integral_mul_const, hmean, zero_mul]
  rw [hval] at hlim
  exact hlim

/-- The covariance of the GFF pairings with `f` and with the dilated test function `κₙ k`,
`wholePlaneGFFCov (pairing f) (pairing (dilateTest n k))`, tends to `0` as `n → ∞` when `∫ k = 0`
(paper lem:mixing, the covariance decay; Duplantier-Sheffield 2011, Section 2.1, eq:cov-kernel). -/
theorem tendsto_wholePlaneGFFCov_dilate {f k : ℂ → ℝ} (hf : IsTestFunction univ f)
    (hk : IsTestFunction univ k) (hmean : ∫ z, k z = 0) :
    Tendsto (fun n : ℕ => wholePlaneGFFCov (GFFObservable.pairing f)
      (GFFObservable.pairing (dilateTest n k))) atTop (𝓝 0) := by
  obtain ⟨R1, hR1⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hk.2.1.isCompact.isBounded
  obtain ⟨R2, hR2⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hf.2.1.isCompact.isBounded
  obtain ⟨R, hRk, hRf⟩ : ∃ R : ℝ, (∀ z, k z ≠ 0 → ‖z‖ ≤ R) ∧ (∀ x, f x ≠ 0 → ‖x‖ ≤ R) :=
    ⟨max R1 R2,
      fun z hz => mem_closedBall_zero_iff.1 (hR1.trans (closedBall_subset_closedBall (le_max_left _ _))
        (subset_tsupport k (Function.mem_support.2 hz))),
      fun x hx => mem_closedBall_zero_iff.1 (hR2.trans (closedBall_subset_closedBall (le_max_right _ _))
        (subset_tsupport f (Function.mem_support.2 hx)))⟩
  have hdecay := tendsto_integral_mul_comp_inv_two_pow (fun w => ∫ x, f x * Real.log ‖x - w‖)
    (continuous_logPotential hf) hk hRk hmean
  have hev : ∀ᶠ n : ℕ in atTop, R ≤ (2 : ℝ) ^ n :=
    tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) R
  have key : (fun n : ℕ => wholePlaneGFFCov (GFFObservable.pairing f)
      (GFFObservable.pairing (dilateTest n k)))
      =ᶠ[atTop] (fun n : ℕ => -∫ z, k z * ∫ x, f x * Real.log ‖x - ((2 : ℝ) ^ n)⁻¹ • z‖) := by
    filter_upwards [hev] with n hn
    have hc := inv_two_pow_mem_Icc n
    have step1 : ∀ x : ℂ, ∫ y, dilateTest n k y * wholePlaneCov x y
        = -∫ z, k z * Real.log ‖x - ((2 : ℝ) ^ n)⁻¹ • z‖ :=
      fun x => integral_dilateTest_wholePlaneCov hk hRk hmean hn x
    have hswap := integral_mul_logPotential_swap hf hk hRf hRk hc.1 hc.2
    show ∫ x, f x * ∫ y, dilateTest n k y * wholePlaneCov x y = _
    calc ∫ x, f x * ∫ y, dilateTest n k y * wholePlaneCov x y
        = ∫ x, -(f x * ∫ z, k z * Real.log ‖x - ((2 : ℝ) ^ n)⁻¹ • z‖) := by
          congr 1
          funext x
          rw [step1 x, mul_neg]
      _ = -∫ x, f x * ∫ z, k z * Real.log ‖x - ((2 : ℝ) ^ n)⁻¹ • z‖ := integral_neg _
      _ = -∫ z, k z * ∫ x, f x * Real.log ‖x - ((2 : ℝ) ^ n)⁻¹ • z‖ := by rw [hswap]
  have hneg := hdecay.neg
  rw [neg_zero] at hneg
  exact hneg.congr' key.symm

end HarmonicBalls
