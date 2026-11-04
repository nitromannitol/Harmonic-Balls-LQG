import HarmonicBalls.Proofs.Sec6.StoppedGeneratorApproximation
import MarkovProcess.Path.Exhaustion

/-! # Exit times along an open-domain exhaustion

A continuous path remains in some member of an increasing open exhaustion
through any compact time interval strictly before exit from the union.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology ZeroAtInfty

/-- Before the exit time of the union, the path remains in one member of an
increasing open exhaustion through the prescribed time. -/
theorem exists_eventually_lt_exitTime_of_open_iUnion
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (ω : ContinuousPath ℂ) (T : ℝ≥0)
    (hT : (T : ℝ≥0∞) < ContinuousPath.exitTime (⋃ n, D n) ω) :
    ∃ N, ∀ n ≥ N, (T : ℝ≥0∞) < ContinuousPath.exitTime (D n) ω := by
  have hcompact : IsCompact ((ω : ℝ≥0 → ℂ) '' Icc 0 T) :=
    isCompact_Icc.image ω.continuous
  have hcover : (ω : ℝ≥0 → ℂ) '' Icc 0 T ⊆ ⋃ n, D n := by
    rintro _ ⟨s, hs, rfl⟩
    apply ContinuousPath.mem_of_lt_exitTime _ ω s
    exact (ENNReal.coe_le_coe.mpr hs.2).trans_lt hT
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover D hopen hcover
  refine ⟨s.sup id, fun n hn => ?_⟩
  have hsub : (ω : ℝ≥0 → ℂ) '' Icc 0 T ⊆ D n := by
    refine hs.trans (iUnion₂_subset fun i hi => hmono ?_)
    exact (Finset.le_sup (f := id) hi).trans hn
  by_contra hle
  rw [not_lt, ContinuousPath.exitTime_le_iff_mem_hitsSetBy (D n) (hopen n) T ω] at hle
  obtain ⟨t, ht⟩ := hle
  exact ht (hsub ⟨t, mem_Icc.mpr ⟨zero_le, t.2⟩, rfl⟩)

/-- Exit times increase to the exit time from the union of an increasing
sequence of open sets. -/
theorem tendsto_exitTime_open_iUnion
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (ω : ContinuousPath ℂ) :
    Tendsto (fun n => ContinuousPath.exitTime (D n) ω) atTop
      (𝓝 (ContinuousPath.exitTime (⋃ n, D n) ω)) := by
  have hsup : (⨆ n, ContinuousPath.exitTime (D n) ω) =
      ContinuousPath.exitTime (⋃ n, D n) ω := by
    apply le_antisymm
    · exact iSup_le fun n => ContinuousPath.exitTime_mono (subset_iUnion D n) ω
    · apply le_of_forall_lt
      intro a ha
      have ha0 : a ≠ ∞ := ne_top_of_lt ha
      let T := a.toNNReal
      have hT : (T : ℝ≥0∞) < ContinuousPath.exitTime (⋃ n, D n) ω := by
        simpa [T, ENNReal.coe_toNNReal ha0] using ha
      obtain ⟨N, hN⟩ := exists_eventually_lt_exitTime_of_open_iUnion hopen hmono ω T hT
      have hle := (hN N le_rfl).trans_le (le_iSup (fun n => ContinuousPath.exitTime (D n) ω) N)
      simpa [T, ENNReal.coe_toNNReal ha0] using hle
  rw [← hsup]
  exact tendsto_atTop_iSup fun n m hnm => ContinuousPath.exitTime_mono (hmono hnm) ω

/-- Bounded continuous functions have convergent Brownian exit expectations
along an increasing exhaustion of a bounded open domain. -/
theorem tendsto_integral_exitTime_open_iUnion
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hbounded : Bornology.IsBounded (⋃ n, D n))
    {q : ℂ → ℝ} (hq : Continuous q) {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M)
    (x : ℂ) :
    Tendsto (fun n => ∫ ω : ContinuousPath ℂ,
      q (ω ((ContinuousPath.exitTime (D n) ω).toNNReal)) ∂(planarBrownianMotion x)) atTop
      (𝓝 (∫ ω : ContinuousPath ℂ,
        q (ω ((ContinuousPath.exitTime (⋃ n, D n) ω).toNNReal))
          ∂(planarBrownianMotion x))) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => M)
  · intro n
    exact (integrable_at_exitTime_of_bounded_measurable (hopen n)
      (hbounded.subset (subset_iUnion D n)) hq.measurable hM x).aestronglyMeasurable
  · exact integrable_const M
  · intro n
    exact Eventually.of_forall fun ω => hM _
  · filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hbounded] with ω hfin
    have ht := tendsto_exitTime_open_iUnion hopen hmono ω
    have ht' := (ENNReal.tendsto_toNNReal hfin.ne).comp ht
    exact hq.continuousAt.tendsto.comp (ω.continuous.continuousAt.tendsto.comp ht')

/-- Local generator-harmonic approximations on an exhaustion imply a stopped
expectation lower bound on the union. -/
theorem le_integral_exitTime_of_local_generator_approximation
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hbounded : Bornology.IsBounded (⋃ n, D n))
    {q : ℂ → ℝ} (hq : Continuous q) {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M)
    {x : ℂ} (hx : x ∈ ⋃ n, D n)
    (happrox : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ y ∈ closure (D n), |q y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
      ∀ y ∈ D n, (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y = 0) :
    q x ≤ ∫ ω : ContinuousPath ℂ,
      q (ω ((ContinuousPath.exitTime (⋃ n, D n) ω).toNNReal)) ∂(planarBrownianMotion x) := by
  obtain ⟨N, hN⟩ := mem_iUnion.mp hx
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_integral_exitTime_open_iUnion hopen hmono hbounded hq hM x)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact le_integral_exitTime_of_generator_approximation (hopen n)
    (hbounded.subset (subset_iUnion D n)) hq.measurable hM (hmono hn hN) (happrox n)

/-- The Green potential has the stopped lower bound if it admits local
    generator-harmonic approximations on an open exhaustion. -/
theorem restricted_greenPotential_stopped_representation_of_local_generator_approximation
    {μ : Measure ℂ} {U L : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : IsCompact L) (hLU : L ⊆ U)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    {x : ℂ} (hx : x ∈ U \ L)
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hunion : (⋃ n, D n) = U \ L)
    (happrox : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ z ∈ closure (D n), |(∫ y in L, greenFunction U z y ∂μ) - (f : C₀(ℂ, ℝ)) z| ≤ ε) ∧
      ∀ z ∈ D n, (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0) :
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
  have hz : ∀ z ∉ U, q z = 0 := by
    intro z hz
    simp only [q, greenFunction_of_notMem_left hz, integral_zero]
  have hc' : ContinuousOn q Uᶜ := by
    apply continuousOn_const.congr
    intro z hz'
    exact hz z hz'
  have hq : Continuous q := by
    rw [← continuousOn_univ]
    have hcover : closure U ∪ Uᶜ = Set.univ := by
      ext z
      simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
      by_cases hzU : z ∈ U
      · exact Or.inl (subset_closure hzU)
      · exact Or.inr hzU
    rw [← hcover]
    exact hc.union_of_isClosed hc' isClosed_closure hU.isClosed_compl
  obtain ⟨M, hM⟩ := (hUb.isCompact_closure).exists_bound_of_continuousOn hc
  have hbound : ∀ z, ‖q z‖ ≤ max M 0 := by
    intro z
    by_cases hmem : z ∈ closure U
    · exact (hM z hmem).trans (le_max_left _ _)
    · rw [hz z (fun hzU => hmem (subset_closure hzU)), norm_zero]
      exact le_max_right _ _
  have hb : Bornology.IsBounded (⋃ n, D n) := by
    rw [hunion]
    exact hUb.subset sdiff_subset
  have hx' : x ∈ ⋃ n, D n := hunion.symm ▸ hx
  have hreal := le_integral_exitTime_of_local_generator_approximation hopen hmono hb hq hbound hx' happrox
  rw [hunion] at hreal
  apply stopped_lintegral_representation_of_integral_representation U L q x ?_
    (integrable_at_exitTime_of_bounded_measurable (hU.sdiff hL.isClosed)
      (hUb.subset sdiff_subset) hq.measurable hbound x) hreal
  intro z
  exact integral_nonneg (greenFunction_nonneg hUb z)

end HarmonicBalls.Section6
