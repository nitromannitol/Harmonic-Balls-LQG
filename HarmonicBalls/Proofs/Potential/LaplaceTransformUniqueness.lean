import Mathlib

/-!
# Uniqueness of the Laplace transform

If two nonnegative functions `φ₁, φ₂`, continuous and bounded on `(0, ∞)`, have the same Laplace
transforms `∫_0^∞ e^{-(n+1) u} φ_i(u) du` for all `n ∈ ℕ`, they agree on `(0, ∞)`
(`eqOn_Ioi_of_laplace_eq`). Under `x = e^{-u}` the finite measures `e^{-u} φ_i(u) du` on `(0, ∞)`
become finite measures on `[0, 1]` with the same moments, which are equal by the Weierstrass
approximation theorem (`ext_of_moments_eq`); so the densities agree almost everywhere, and then
everywhere on `(0, ∞)` by continuity.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- Continuous functions are integrable for a finite measure carried by `[0, 1]`. -/
theorem integrable_of_continuous_of_ae_mem_Icc {m : Measure ℝ} [IsFiniteMeasure m]
    (hm : ∀ᵐ x ∂m, x ∈ Icc (0 : ℝ) 1) {g : ℝ → ℝ} (hg : Continuous g) : Integrable g m := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  exact Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (hm.mono fun x hx => hC x hx)

/-- **Finite measures on `ℝ` carried by `[0, 1]` with the same moments are equal**, by the
Weierstrass approximation theorem. -/
theorem ext_of_moments_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Icc 0 1)ᶜ = 0) (hν : ν (Icc 0 1)ᶜ = 0)
    (h : ∀ n : ℕ, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) : μ = ν := by
  have hμI : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hμ
  have hνI : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hν
  have hpoly : ∀ p : Polynomial ℝ, ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν := by
    intro p
    simp_rw [Polynomial.eval_eq_sum_range]
    have hi : ∀ (m : Measure ℝ) [IsFiniteMeasure m], (∀ᵐ x ∂m, x ∈ Icc (0 : ℝ) 1) →
        ∀ i ∈ Finset.range (p.natDegree + 1), Integrable (fun x : ℝ => p.coeff i * x ^ i) m :=
      fun m _ hm i _ => integrable_of_continuous_of_ae_mem_Icc hm
        (continuous_const.mul (continuous_pow i))
    rw [integral_finsetSum _ (hi μ hμI), integral_finsetSum _ (hi ν hνI)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_const_mul, h i]
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hest : ∀ (m : Measure ℝ) [IsFiniteMeasure m], (∀ᵐ x ∂m, x ∈ Icc (0 : ℝ) 1) →
      ∀ (p : Polynomial ℝ) (δ : ℝ), (∀ x ∈ Icc (0 : ℝ) 1, |p.eval x - f x| < δ) →
        dist (∫ x, f x ∂m) (∫ x, p.eval x ∂m) ≤ δ * (m univ).toReal := by
    intro m _ hm p δ hp
    rw [dist_eq_norm, ← integral_sub (integrable_of_continuous_of_ae_mem_Icc hm f.continuous)
      (integrable_of_continuous_of_ae_mem_Icc hm p.continuous)]
    refine (norm_integral_le_of_norm_le (integrable_const δ) (hm.mono fun x hx => ?_)).trans ?_
    · rw [Real.norm_eq_abs, abs_sub_comm]
      exact (hp x hx).le
    · rw [integral_const, smul_eq_mul, mul_comm, Measure.real]
  refine eq_of_forall_dist_le fun ε hε => ?_
  set M := (μ univ).toReal + (ν univ).toReal + 1 with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f f.continuous.continuousOn
    (ε / M) (by positivity)
  calc dist (∫ x, f x ∂μ) (∫ x, f x ∂ν)
      ≤ dist (∫ x, f x ∂μ) (∫ x, p.eval x ∂μ) + dist (∫ x, p.eval x ∂ν) (∫ x, f x ∂ν) := by
        rw [← hpoly p]
        exact dist_triangle _ _ _
    _ ≤ ε / M * (μ univ).toReal + ε / M * (ν univ).toReal := by
        rw [dist_comm (∫ x, p.eval x ∂ν)]
        exact add_le_add (hest μ hμI p _ hp) (hest ν hνI p _ hp)
    _ ≤ ε := by
        rw [← mul_add, div_mul_eq_mul_div, div_le_iff₀ hM0]
        exact mul_le_mul_of_nonneg_left (by linarith) hε.le

/-- `∫_0^∞ e^{-u} du = 1`. -/
theorem lintegral_Ioi_ofReal_exp_neg : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-u)) = 1 := by
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun u => (Real.exp_pos _).le),
    integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

/-- **Uniqueness of the Laplace transform.** Nonnegative functions, continuous and bounded on
`(0, ∞)`, with the same Laplace transforms at `1, 2, 3, …` agree on `(0, ∞)`. -/
theorem eqOn_Ioi_of_laplace_eq {φ₁ φ₂ : ℝ → ℝ} (h1c : ContinuousOn φ₁ (Ioi 0))
    (h2c : ContinuousOn φ₂ (Ioi 0)) (h10 : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ φ₁ u)
    (h20 : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ φ₂ u) {B : ℝ} (h1B : ∀ u ∈ Ioi (0 : ℝ), φ₁ u ≤ B)
    (h2B : ∀ u ∈ Ioi (0 : ℝ), φ₂ u ≤ B)
    (hL : ∀ n : ℕ, ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-((n + 1) * u))) *
      ENNReal.ofReal (φ₁ u) = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-((n + 1) * u))) *
        ENNReal.ofReal (φ₂ u)) :
    EqOn φ₁ φ₂ (Ioi 0) := by
  have hIoi : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
  have hE : Measurable fun u : ℝ => Real.exp (-u) := Real.continuous_exp.measurable.comp measurable_neg
  -- the measures `e^{-u} φ_i(u) du` on `(0, ∞)`
  set w : (ℝ → ℝ) → ℝ → ℝ≥0∞ := fun φ u => ENNReal.ofReal (Real.exp (-u)) * ENNReal.ofReal (φ u)
    with hw
  have hwm : ∀ φ : ℝ → ℝ, ContinuousOn φ (Ioi 0) → AEMeasurable (w φ) (volume.restrict (Ioi 0)) :=
    fun φ hφ => (hE.ennreal_ofReal.aemeasurable).mul
      (hφ.aemeasurable hIoi).ennreal_ofReal
  set W : (ℝ → ℝ) → Measure ℝ := fun φ => (volume.restrict (Ioi (0 : ℝ))).withDensity (w φ) with hW
  have hWfin : ∀ φ : ℝ → ℝ, (∀ u ∈ Ioi (0 : ℝ), φ u ≤ B) → W φ univ ≠ ⊤ := by
    intro φ hB
    rw [hW, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    refine ne_top_of_le_ne_top (b := ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-u)) *
      ENNReal.ofReal B) ?_ (setLIntegral_mono' hIoi fun u hu =>
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hB u hu)))
    rw [lintegral_mul_const _ hE.ennreal_ofReal, lintegral_Ioi_ofReal_exp_neg, one_mul]
    exact ENNReal.ofReal_ne_top
  -- their images under `u ↦ e^{-u}`
  set V : (ℝ → ℝ) → Measure ℝ := fun φ => (W φ).map fun u => Real.exp (-u) with hV
  have hVfin : ∀ φ : ℝ → ℝ, (∀ u ∈ Ioi (0 : ℝ), φ u ≤ B) → IsFiniteMeasure (V φ) := by
    intro φ hB
    refine ⟨?_⟩
    rw [hV, Measure.map_apply hE MeasurableSet.univ, preimage_univ]
    exact lt_top_iff_ne_top.2 (hWfin φ hB)
  have hVI : ∀ φ : ℝ → ℝ, V φ (Icc 0 1)ᶜ = 0 := by
    intro φ
    rw [hV, Measure.map_apply hE (isClosed_Icc.measurableSet.compl), hW,
      withDensity_apply _ (hE (isClosed_Icc.measurableSet.compl))]
    refine setLIntegral_measure_zero _ _ ?_
    rw [Measure.restrict_apply (hE (isClosed_Icc.measurableSet.compl))]
    refine measure_mono_null (fun u hu => ?_) measure_empty
    exact hu.1 ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (neg_nonpos.2 (le_of_lt hu.2))⟩
  have hVmom : ∀ φ : ℝ → ℝ, ContinuousOn φ (Ioi 0) → (∀ u ∈ Ioi (0 : ℝ), 0 ≤ φ u) →
      ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (x ^ n) ∂V φ = ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-((n + 1) * u))) * ENNReal.ofReal (φ u) := by
    intro φ hφ h0 n
    show ∫⁻ x, ENNReal.ofReal (x ^ n) ∂((W φ).map fun u => Real.exp (-u)) = _
    rw [lintegral_map (f := fun x : ℝ => ENNReal.ofReal (x ^ n)) (by fun_prop) hE]
    show ∫⁻ u, ENNReal.ofReal (Real.exp (-u) ^ n)
      ∂((volume.restrict (Ioi (0 : ℝ))).withDensity (w φ)) = _
    rw [lintegral_withDensity_eq_lintegral_mul₀ (hwm φ hφ)
        (g := fun u : ℝ => ENNReal.ofReal (Real.exp (-u) ^ n)) (by fun_prop)]
    refine setLIntegral_congr_fun hIoi fun u hu => ?_
    simp only [Pi.mul_apply, hw]
    rw [mul_comm (ENNReal.ofReal (Real.exp (-u))), mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_nat_mul, ← Real.exp_add, mul_comm]
    congr 2
    ring
  have hμ1 := hVfin φ₁ h1B
  have hμ2 := hVfin φ₂ h2B
  have hVeq : V φ₁ = V φ₂ := by
    refine ext_of_moments_eq (hVI φ₁) (hVI φ₂) fun n => ?_
    have hnn : ∀ φ : ℝ → ℝ, 0 ≤ᵐ[V φ] fun x : ℝ => x ^ n := by
      intro φ
      have hI : ∀ᵐ x ∂V φ, x ∈ Icc (0 : ℝ) 1 := by
        rw [ae_iff]
        exact hVI φ
      exact hI.mono fun x hx => pow_nonneg hx.1 n
    rw [integral_eq_lintegral_of_nonneg_ae (hnn φ₁) (continuous_pow n).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (hnn φ₂) (continuous_pow n).aestronglyMeasurable,
      hVmom φ₁ h1c h10 n, hVmom φ₂ h2c h20 n, hL n]
  -- back to `(0, ∞)`
  have hWeq : W φ₁ = W φ₂ := by
    have hback : ∀ φ : ℝ → ℝ, (V φ).map (fun x => -Real.log x) = W φ := by
      intro φ
      show ((W φ).map fun u => Real.exp (-u)).map (fun x => -Real.log x) = W φ
      rw [Measure.map_map (show Measurable fun x : ℝ => -Real.log x from Real.measurable_log.neg)
        hE]
      have : ((fun x => -Real.log x) ∘ fun u : ℝ => Real.exp (-u)) = id := by
        funext u
        simp [Real.log_exp]
      rw [this, Measure.map_id]
    rw [← hback φ₁, ← hback φ₂, hVeq]
  have hae : w φ₁ =ᵐ[volume.restrict (Ioi 0)] w φ₂ := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (hwm φ₁ h1c) (hwm φ₂ h2c)
      fun S hS _ => ?_
    have h := congrArg (fun m : Measure ℝ => m S) hWeq
    simp only [hW, withDensity_apply _ hS] at h
    exact h
  have hae' : φ₁ =ᵐ[volume.restrict (Ioi 0)] φ₂ := by
    filter_upwards [hae, ae_restrict_mem hIoi] with u hu hu0
    simp only [hw] at hu
    have hne : ENNReal.ofReal (Real.exp (-u)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.exp_pos _
    have h := (ENNReal.mul_right_inj hne ENNReal.ofReal_ne_top).1 hu
    exact (ENNReal.ofReal_eq_ofReal_iff (h10 u hu0) (h20 u hu0)).1 h
  refine Measure.eqOn_of_ae_eq hae' h1c h2c ?_
  rw [interior_Ioi]
  exact subset_closure

end HarmonicBalls
