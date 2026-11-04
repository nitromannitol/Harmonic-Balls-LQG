import HarmonicBalls.Proofs.Sec6.LocalSubharmonicApproximation
import HarmonicBalls.Proofs.Sec6.RelativelyCompactExhaustion
import HarmonicBalls.Steps.Sec4.Basic
import HarmonicBalls.Steps.Sec3.LeastSupersolutionMem

/-! # Odometer comparison via local generator approximations -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology ZeroAtInfty

/-- A pole-avoiding component satisfies the odometer harmonic-measure bound
under local nonnegative-generator approximations on an exhaustion. -/
theorem odometer_le_harmonicMeasure_of_local_generator_approximation
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {A : Set ℂ} (hA : IsOpen A) (hAin : A ⊆ ball (0 : ℂ) 1)
    (hAsub : closure A ⊆ closedBall (0 : ℂ) 1 \ {z})
    {x : ℂ} (hx : x ∈ A ∩ cluster μ 1 z t)
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hunion : (⋃ n, D n) = connectedComponentIn (A ∩ cluster μ 1 z t) x)
    (happrox : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ y ∈ closure (D n), |(closure A).indicator (fun y => max 0 (odometer μ 1 z t y)) y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
      ∀ y ∈ D n, 0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y) :
    odometerExt μ z t x ≤
      (⨆ y ∈ frontier A ∩ closure (connectedComponentIn (A ∩ cluster μ 1 z t) x),
        odometerExt μ z t y) *
        planarBrownianMotion x {ω | ContinuousPath.exitTime A ω ≤
          hittingTime (A \ connectedComponentIn (A ∩ cluster μ 1 z t) x) ω} := by
  classical
  have hAb : Bornology.IsBounded A :=
    isBounded_ball.subset hAin
  let Y := connectedComponentIn (A ∩ cluster μ 1 z t) x
  let q := (closure A).indicator (fun y => max 0 (odometer μ 1 z t y))
  have hωcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ zero_lt_one hV hz ht).1
  have hYopen : IsOpen Y := (hA.inter hωcluster).connectedComponentIn
  have hYsub : Y ⊆ A ∩ cluster μ 1 z t := connectedComponentIn_subset _ _
  have hxY : x ∈ Y := mem_connectedComponentIn hx
  have hYcomp : ∀ y ∈ Y, connectedComponentIn (A ∩ cluster μ 1 z t) y ⊆ Y := by
    intro y hy
    exact (connectedComponentIn_eq hy).symm.subset
  have hdis : Disjoint (frontier Y) (A ∩ cluster μ 1 z t) :=
    frontier_union_components_disjoint (hA.inter hωcluster) hYsub hYcomp
  obtain ⟨_, hvc, _⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ zero_lt_one hV hz ht
  have hc := (continuousOn_odometer greenFunctionBall zero_lt_one hz hvc).mono hAsub
  have hqc : ContinuousOn q (closure A) := by
    apply hc.congr
    intro y hy
    have hyunit := hAsub hy
    have hnonneg := odometer_nonneg (μ := μ) ht.le hyunit.1 hyunit.2
    simp [q, hy, max_eq_right hnonneg]
  have hqzero : ∀ y ∉ closure A, q y = 0 := by intro y hy; simp [q, hy]
  have hqmeas : Measurable q := measurable_of_continuousOn_closure_of_zero hqc hqzero
  have hqnonneg : ∀ y, 0 ≤ q y := by
    intro y
    by_cases hy : y ∈ closure A
    · simp only [q, indicator_of_mem hy]; exact le_max_left _ _
    · simp [q, hy]
  obtain ⟨M, hM⟩ := hAb.isCompact_closure.exists_bound_of_continuousOn hqc
  have hM' : ∀ y, ‖q y‖ ≤ max M 0 := by
    intro y
    by_cases hy : y ∈ closure A
    · exact (hM y hy).trans (le_max_left _ _)
    · rw [hqzero y hy, norm_zero]; exact le_max_right _ _
  have hzero : ∀ y ∈ A ∩ frontier Y, q y = 0 := by
    intro y hy
    have hyoutside : y ∉ cluster μ 1 z t := by
      intro hycluster
      exact disjoint_left.mp hdis hy.2 ⟨hy.1, hycluster⟩
    have hyunit := hAsub (subset_closure hy.1)
    have hyz : y ≠ z := by simpa using hyunit.2
    have hnonneg := odometer_nonneg (μ := μ) ht.le hyunit.1 hyunit.2
    have hnonpos : odometer μ 1 z t y ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      exact hyoutside (mem_cluster_iff.mpr ⟨hAin hy.1, Or.inr hpos⟩)
    have hz' : odometer μ 1 z t y = 0 := le_antisymm hnonpos hnonneg
    simp [q, subset_closure hy.1, hz']
  have hbound : ∀ y ∈ frontier A ∩ closure Y,
      ENNReal.ofReal (q y) ≤ ⨆ y ∈ frontier A ∩ closure Y, odometerExt μ z t y := by
    intro y hy
    have hycl := frontier_subset_closure hy.1
    have hyunit := hAsub hycl
    have hyz : y ≠ z := by simpa using hyunit.2
    have hnonneg := odometer_nonneg (μ := μ) ht.le hyunit.1 hyunit.2
    have heq : ENNReal.ofReal (q y) = odometerExt μ z t y := by
      simp [q, hycl, max_eq_right hnonneg, odometerExt, hyz]
    rw [heq]
    exact le_iSup₂_of_le y hy le_rfl
  have hxunit := hAsub (subset_closure hx.1)
  have hxz : x ≠ z := by simpa using hxunit.2
  have hxnonneg := odometer_nonneg (μ := μ) ht.le hxunit.1 hxunit.2
  have hxq : ENNReal.ofReal (q x) = odometerExt μ z t x := by
    simp [q, subset_closure hx.1, max_eq_right hxnonneg, odometerExt, hxz]
  rw [← hxq]
  have hDA : (⋃ n, D n) ⊆ A := hunion ▸ hYsub.trans inter_subset_left
  have hxD : x ∈ ⋃ n, D n := hunion ▸ hxY
  have hzero' : ∀ y ∈ A ∩ frontier (⋃ n, D n), q y = 0 := by
    simpa only [hunion] using hzero
  have hbound' : ∀ y ∈ frontier A ∩ closure (⋃ n, D n),
      ENNReal.ofReal (q y) ≤ ⨆ y ∈ frontier A ∩ closure Y, odometerExt μ z t y := by
    simpa only [hunion] using hbound
  have hresult := ofReal_le_boundary_mul_harmonicMeasure_of_local_generator_approximation
    hopen hmono hA hAb hDA hqc hqmeas hqnonneg hM' hzero' hbound' hxD happrox
  simpa only [hunion] using hresult


/-- Compact-local nonnegative-generator approximations suffice for the
odometer harmonic-measure comparison on a pole-avoiding domain. -/
theorem odometer_le_harmonicMeasure_of_compact_local_generator_approximation
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {A : Set ℂ} (hA : IsOpen A) (hAin : A ⊆ ball (0 : ℂ) 1)
    (hAsub : closure A ⊆ closedBall (0 : ℂ) 1 \ {z})
    {x : ℂ} (hx : x ∈ A ∩ cluster μ 1 z t)
    (happrox : ∀ (V : Set ℂ), IsOpen V → IsCompact (closure V) →
      closure V ⊆ connectedComponentIn (A ∩ cluster μ 1 z t) x →
      ∀ ε : ℝ, 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ y ∈ closure V, |(closure A).indicator (fun y => max 0 (odometer μ 1 z t y)) y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
        ∀ y ∈ V, 0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y) :
    odometerExt μ z t x ≤
      (⨆ y ∈ frontier A ∩ closure (connectedComponentIn (A ∩ cluster μ 1 z t) x),
        odometerExt μ z t y) *
        planarBrownianMotion x {ω | ContinuousPath.exitTime A ω ≤
          hittingTime (A \ connectedComponentIn (A ∩ cluster μ 1 z t) x) ω} := by
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ zero_lt_one hV hz ht).1
  have hYopen : IsOpen (connectedComponentIn (A ∩ cluster μ 1 z t) x) :=
    (hA.inter hcluster).connectedComponentIn
  obtain ⟨D, hDopen, hDmono, hDcompact, hDnext, hDunion⟩ :=
    exists_relativelyCompact_open_exhaustion hYopen
  apply odometer_le_harmonicMeasure_of_local_generator_approximation hμ hV hz ht hA hAin hAsub hx
    hDopen hDmono hDunion
  intro n ε hε
  apply happrox (D n) (hDopen n) (hDcompact n) _ ε hε
  exact (hDnext n).trans (hDunion ▸ subset_iUnion D (n + 1))

end HarmonicBalls.Section6
