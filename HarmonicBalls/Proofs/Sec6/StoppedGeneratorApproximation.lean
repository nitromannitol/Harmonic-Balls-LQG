import HarmonicBalls.Proofs.Sec6.StoppedPotentialIntegrability
import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller
import MarkovProcess.Trajectory.HarmonicRepresentation

/-! # Stopped expectations from generator approximations

Uniform approximation on the stopped domain by generator-domain functions
whose generators vanish there transfers the Feller harmonic representation to
a bounded measurable function.

The approximation premise is restrictive. For a nowhere-dense obstacle `L`,
continuity of the generator forces it to vanish on all of `U` if it vanishes
on `U \ L`. Thus such approximants cannot generally approximate a nonzero
Green potential with zero boundary values: the maximum principle forces a
uniform limit of these harmonic functions with zero boundary values to vanish.
This result does not establish the needed approximations for arbitrary `L`;
an exhaustion by smaller open subsets is a possible local route.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology ZeroAtInfty

/-- Uniform approximation by generator-harmonic functions implies the
truncated and full Brownian exit expectations dominate the initial value. -/
theorem le_integral_exitTime_of_generator_approximation
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {q : ℂ → ℝ} (hq : Measurable q) {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M)
    {x : ℂ} (hx : x ∈ D)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ y ∈ closure D, |q y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
      ∀ y ∈ D, (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y = 0) :
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
  have heq : (∫ ω : ContinuousPath ℂ, g (ω (T ω)) ∂(planarBrownianMotion x)) = g x := by
    rw [planarBrownianMotion_eq_continuousProcess]
    exact isFellerKernelSemigroup_planarHeatSemigroup.integral_eval_exitTimeTrunc_eq_of_generator_eq_zero
      isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup f D hD hfgen n x
  rw [heq, integral_add hqint (integrable_const _)] at hle
  simp only [integral_const, probReal_univ, one_smul] at hle
  have hxapprox := hfapprox x (subset_closure hx)
  dsimp [g] at hle
  linarith [abs_le.mp hxapprox]


/-- The restricted Green potential satisfies the stopped representation when
it can be uniformly approximated by generator-harmonic functions on the
punctured domain. -/
theorem restricted_greenPotential_stopped_representation_of_generator_approximation
    {μ : Measure ℂ} {U L : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : IsCompact L) (hLU : L ⊆ U)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    {x : ℂ} (hx : x ∈ U \ L)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ z ∈ closure (U \ L), |(∫ y in L, greenFunction U z y ∂μ) - (f : C₀(ℂ, ℝ)) z| ≤ ε) ∧
      ∀ z ∈ U \ L, (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0) :
    ENNReal.ofReal (∫ y in L, greenFunction U x y ∂μ) ≤ ∫⁻ ω,
      ENNReal.ofReal (∫ y in L,
        greenFunction U (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)) y ∂μ)
          ∂(planarBrownianMotion x) := by
  let q : ℂ → ℝ := fun z => ∫ y in L, greenFunction U z y ∂μ
  obtain ⟨_, C, t, ht, hcont⟩ := hholder (L.indicator (fun _ => 1))
    ((memLp_top_const (1 : ℝ)).indicator hL.measurableSet)
  have heq : (fun z => ∫ y in U, greenFunction U z y * L.indicator (fun _ => 1) y ∂μ) = q := by
    funext z
    have hind : (fun y => greenFunction U z y * L.indicator (fun _ => 1) y) =
        L.indicator (greenFunction U z) := by
      funext y
      by_cases hy : y ∈ L <;> simp [hy]
    rw [hind, integral_indicator hL.measurableSet, Measure.restrict_restrict_of_subset hLU]
  rw [heq] at hcont
  have hc := hcont.continuousOn ht
  have hz : ∀ z ∉ closure U, q z = 0 := by
    intro z hz
    have hzU : z ∉ U := fun hzU => hz (subset_closure hzU)
    simp only [q, greenFunction_of_notMem_left hzU, integral_zero]
  have hq := measurable_of_continuousOn_closure_of_zero hc hz
  obtain ⟨M, hM⟩ := (hUb.isCompact_closure).exists_bound_of_continuousOn hc
  have hbound : ∀ z, ‖q z‖ ≤ max M 0 := by
    intro z
    by_cases hmem : z ∈ closure U
    · exact (hM z hmem).trans (le_max_left _ _)
    · rw [hz z hmem, norm_zero]
      exact le_max_right _ _
  have hD := hU.sdiff hL.isClosed
  have hDb := hUb.subset (sdiff_subset : U \ L ⊆ U)
  have hreal := le_integral_exitTime_of_generator_approximation hD hDb hq hbound hx happrox
  apply stopped_lintegral_representation_of_integral_representation U L q x ?_
    (integrable_at_exitTime_of_bounded_measurable hD hDb hq hbound x) hreal
  intro z
  exact integral_nonneg (greenFunction_nonneg hUb z)

end HarmonicBalls.Section6
