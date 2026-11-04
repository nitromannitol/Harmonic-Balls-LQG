import HarmonicBalls.Proofs.Sec6.StoppedGeneratorApproximation

/-! # Stopped subharmonic approximations

Dynkin's formula gives a lower bound on the stopped expectation for generator
domain functions whose generator is nonnegative before exit.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology ZeroAtInfty

/-- A generator-domain function with nonnegative generator is dominated by its
truncated Brownian exit expectation. -/
theorem le_integral_exitTimeTrunc_of_generator_nonneg
    {D : Set ℂ} (hD : IsOpen D)
    (f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain)
    (hgen : ∀ y ∈ D, 0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y)
    (K : ℝ≥0) (x : ℂ) :
    (f : C₀(ℂ, ℝ)) x ≤ ∫ ω : ContinuousPath ℂ,
      (f : C₀(ℂ, ℝ)) (ω (ContinuousPath.exitTimeTrunc D K ω)) ∂(planarBrownianMotion x) := by
  rw [planarBrownianMotion_eq_continuousProcess]
  have hdyn := isFellerKernelSemigroup_planarHeatSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator
    isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup f
    (ContinuousPath.exitTimeTrunc D K) (ContinuousPath.isStoppingTime_exitTimeTrunc D hD K)
    (ContinuousPath.exitTimeTrunc_le D K) x
  have hpath : ∀ ω : ContinuousPath ℂ, 0 ≤ ∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D K ω : ℝ),
      (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) (ω (Real.toNNReal s)) := by
    intro ω
    apply intervalIntegral.integral_nonneg_of_ae_restrict (ContinuousPath.exitTimeTrunc D K ω).coe_nonneg
    change ∀ᵐ s : ℝ ∂volume.restrict (Icc 0 (ContinuousPath.exitTimeTrunc D K ω : ℝ)),
      0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) (ω (Real.toNNReal s))
    rw [ae_restrict_iff' measurableSet_Icc]
    have hsingle : ∀ᵐ s : ℝ ∂volume, s ≠ (ContinuousPath.exitTimeTrunc D K ω : ℝ) := by
      rw [ae_iff]
      simpa only [Ne, not_not, Set.ofPred_eq_eq_singleton] using
        measure_singleton (ContinuousPath.exitTimeTrunc D K ω : ℝ)
    filter_upwards [hsingle] with s hs hmem
    apply hgen
    apply ContinuousPath.mem_of_lt_exitTimeTrunc
    exact (Real.toNNReal_lt_iff_lt_coe hmem.1).mpr (lt_of_le_of_ne hmem.2 hs)
  have hnonneg : 0 ≤ ∫ ω : ContinuousPath ℂ,
      (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc D K ω : ℝ),
        (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) (ω (Real.toNNReal s)))
      ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess planarHeatSemigroup
        isConservative_planarHeatSemigroup x) := integral_nonneg hpath
  linarith only [hdyn, hnonneg]

/-- Uniform approximation on the stopped domain by generator-subharmonic
functions transfers the exit expectation inequality. -/
theorem le_integral_exitTime_of_generator_nonneg_approximation
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {q : ℂ → ℝ} (hq : Measurable q) {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M)
    {x : ℂ} (hx : x ∈ D)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ y ∈ closure D, |q y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
      ∀ y ∈ D, 0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y) :
    q x ≤ ∫ ω : ContinuousPath ℂ,
      q (ω ((ContinuousPath.exitTime D ω).toNNReal)) ∂(planarBrownianMotion x) := by
  apply integral_exitTime_lower_of_truncations hD hDb hq hM x
  intro n
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨f, hfapprox, hfgen⟩ := happrox (ε / 2) (by positivity)
  let g : C₀(ℂ, ℝ) := f
  let T : ContinuousPath ℂ → ℝ≥0 := ContinuousPath.exitTimeTrunc D n
  have hT := ContinuousPath.isStoppingTime_exitTimeTrunc D hD n
  have hqint : Integrable (fun ω : ContinuousPath ℂ => q (ω (T ω))) (planarBrownianMotion x) := by
    apply Integrable.of_bound ((hq.comp (ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable) M
    exact Eventually.of_forall fun ω => hM _
  have hfint : Integrable (fun ω : ContinuousPath ℂ => g (ω (T ω))) (planarBrownianMotion x) := by
    apply Integrable.of_bound ((g.continuous.measurable.comp
      (ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable) ‖g‖
    exact Eventually.of_forall fun ω => g.toBCF.norm_coe_le_norm _
  have hle : (∫ ω : ContinuousPath ℂ, g (ω (T ω)) ∂(planarBrownianMotion x)) ≤
      ∫ ω : ContinuousPath ℂ, (q (ω (T ω)) + ε / 2) ∂(planarBrownianMotion x) := by
    apply integral_mono_ae hfint (hqint.add (integrable_const _))
    filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω h0
    have hmem : ω (T ω) ∈ closure D :=
      ContinuousPath.stopped_exitTimeTrunc_mem_closure D hD n ω (h0 ▸ hx)
    have h := hfapprox _ hmem
    dsimp [g] at h ⊢
    linarith [abs_le.mp h]
  have hlow : g x ≤ ∫ ω : ContinuousPath ℂ, g (ω (T ω)) ∂(planarBrownianMotion x) :=
    le_integral_exitTimeTrunc_of_generator_nonneg hD f hfgen n x
  rw [integral_add hqint (integrable_const _)] at hle
  simp only [integral_const, probReal_univ, one_smul] at hle
  have hxapprox := hfapprox x (subset_closure hx)
  dsimp [g] at hle hlow
  linarith [abs_le.mp hxapprox]

end HarmonicBalls.Section6
