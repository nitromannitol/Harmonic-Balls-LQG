import HarmonicBalls.Proofs.Sec6.ExitTimeExhaustion
import HarmonicBalls.Proofs.Sec6.GeneratorHarmonicMeasure

/-! # Subharmonic approximation on an open exhaustion -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology ZeroAtInfty

/-- Exit expectations converge along an exhaustion when the function is
continuous on the closure of a containing domain. -/
theorem tendsto_integral_exitTime_open_iUnion_of_continuousOn
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    {A : Set ℂ} (hDA : (⋃ n, D n) ⊆ A) (hAb : Bornology.IsBounded A)
    {q : ℂ → ℝ} (hq : ContinuousOn q (closure A)) (hqmeas : Measurable q)
    {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M) {x : ℂ} (hx : x ∈ ⋃ n, D n) :
    Tendsto (fun n => ∫ ω : ContinuousPath ℂ,
      q (ω ((ContinuousPath.exitTime (D n) ω).toNNReal)) ∂(planarBrownianMotion x)) atTop
      (𝓝 (∫ ω : ContinuousPath ℂ,
        q (ω ((ContinuousPath.exitTime (⋃ n, D n) ω).toNNReal))
          ∂(planarBrownianMotion x))) := by
  have hDb := hAb.subset hDA
  obtain ⟨N, hN⟩ := mem_iUnion.mp hx
  apply tendsto_integral_of_dominated_convergence (fun _ => M)
  · intro n
    exact (integrable_at_exitTime_of_bounded_measurable (hopen n)
      (hDb.subset (subset_iUnion D n)) hqmeas hM x).aestronglyMeasurable
  · exact integrable_const M
  · intro n
    exact Eventually.of_forall fun ω => hM _
  · filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hDb,
      ae_planarBrownianMotion_eval_zero x] with ω hfin hstart
    have ht := tendsto_exitTime_open_iUnion hopen hmono ω
    have ht' := (ENNReal.tendsto_toNNReal hfin.ne).comp ht
    have hcoords := ω.continuous.continuousAt.tendsto.comp ht'
    have hpoint : ω ((ContinuousPath.exitTime (⋃ n, D n) ω).toNNReal) ∈ closure A :=
      closure_mono hDA (frontier_subset_closure
        (ContinuousPath.coordinate_exitTime_mem_frontier (⋃ n, D n) (isOpen_iUnion hopen)
          ω (hstart ▸ hx) hfin.ne))
    apply (hq _ hpoint).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hcoords, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    apply closure_mono ((subset_iUnion D n).trans hDA)
    apply frontier_subset_closure
    apply ContinuousPath.coordinate_exitTime_mem_frontier (D n) (hopen n) ω
    · exact hstart ▸ hmono hn hN
    · exact ne_top_of_le_ne_top hfin.ne (ContinuousPath.exitTime_mono (subset_iUnion D n) ω)

/-- Local approximation by functions with nonnegative generator gives an
exit expectation lower bound on the union. -/
theorem le_integral_exitTime_of_local_generator_nonneg_approximation
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    {A : Set ℂ} (hDA : (⋃ n, D n) ⊆ A) (hAb : Bornology.IsBounded A)
    {q : ℂ → ℝ} (hq : ContinuousOn q (closure A)) (hqmeas : Measurable q)
    {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M) {x : ℂ} (hx : x ∈ ⋃ n, D n)
    (happrox : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ y ∈ closure (D n), |q y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
      ∀ y ∈ D n, 0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y) :
    q x ≤ ∫ ω : ContinuousPath ℂ,
      q (ω ((ContinuousPath.exitTime (⋃ n, D n) ω).toNNReal)) ∂(planarBrownianMotion x) := by
  obtain ⟨N, hN⟩ := mem_iUnion.mp hx
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_integral_exitTime_open_iUnion_of_continuousOn hopen hmono hDA hAb hq hqmeas hM hx)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact le_integral_exitTime_of_generator_nonneg_approximation (hopen n)
    (hAb.subset ((subset_iUnion D n).trans hDA)) hqmeas hM (hmono hn hN) (happrox n)

/-- An exhaustion by generator-subharmonic approximations implies the boundary
harmonic-measure estimate. -/
theorem ofReal_le_boundary_mul_harmonicMeasure_of_local_generator_approximation
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    {A : Set ℂ} (hA : IsOpen A) (hAb : Bornology.IsBounded A)
    (hDA : (⋃ n, D n) ⊆ A) {q : ℂ → ℝ} (hq : ContinuousOn q (closure A))
    (hqmeas : Measurable q) (hqnonneg : ∀ y, 0 ≤ q y)
    {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M) {B : ℝ≥0∞}
    (hzero : ∀ y ∈ A ∩ frontier (⋃ n, D n), q y = 0)
    (hbound : ∀ y ∈ frontier A ∩ closure (⋃ n, D n), ENNReal.ofReal (q y) ≤ B)
    {x : ℂ} (hx : x ∈ ⋃ n, D n)
    (happrox : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ y ∈ closure (D n), |q y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
      ∀ y ∈ D n, 0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y) :
    ENNReal.ofReal (q x) ≤ B * planarBrownianMotion x
      {ω | ContinuousPath.exitTime A ω ≤ hittingTime (A \ (⋃ n, D n)) ω} :=
  ofReal_le_boundary_mul_harmonicMeasure_of_exitExpectation hA (isOpen_iUnion hopen)
    hAb hDA hqmeas hqnonneg hM hzero hbound hx
    (le_integral_exitTime_of_local_generator_nonneg_approximation hopen hmono hDA hAb hq hqmeas hM hx happrox)

end HarmonicBalls.Section6
