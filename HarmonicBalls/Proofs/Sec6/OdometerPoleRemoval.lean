import HarmonicBalls.Proofs.Sec6.BoundaryHarmonicMeasureMonotonicity
import HarmonicBalls.Proofs.Sec6.LocalOdometerApproximation

/-! # Removing the pole from the closure of a comparison domain -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology ZeroAtInfty

/-- A finite boundary supremum permits the odometer comparison to be proved
using compact-local generator approximations, even if the pole lies in the
closure of the original domain. -/
theorem odometer_le_harmonicMeasure_of_compact_local_approximation_and_finite_boundary
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {A : Set ℂ} (hA : IsOpen A) (hAin : A ⊆ ball (0 : ℂ) 1) (hzA : z ∉ A)
    {x : ℂ} (hx : x ∈ A ∩ cluster μ 1 z t)
    (hfinite : (⨆ y ∈ frontier A ∩ closure (connectedComponentIn (A ∩ cluster μ 1 z t) x),
      odometerExt μ z t y) ≠ ⊤)
    (happrox : ∀ (V : Set ℂ), IsOpen V → IsCompact (closure V) →
      closure V ⊆ connectedComponentIn (A ∩ cluster μ 1 z t) x →
      ∀ ε : ℝ, 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ y ∈ closure V, |odometer μ 1 z t y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
        ∀ y ∈ V, 0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y) :
    odometerExt μ z t x ≤
      (⨆ y ∈ frontier A ∩ closure (connectedComponentIn (A ∩ cluster μ 1 z t) x),
        odometerExt μ z t y) *
        planarBrownianMotion x {ω | ContinuousPath.exitTime A ω ≤
          hittingTime (A \ connectedComponentIn (A ∩ cluster μ 1 z t) x) ω} := by
  classical
  let Y := connectedComponentIn (A ∩ cluster μ 1 z t) x
  obtain ⟨A', hA'o, hA'sub, hzA', hfront, hcomponent⟩ :=
    exists_pole_avoiding_domain_with_same_component hA hzA hx hfinite
  have hYsubA' : Y ⊆ A' := by
    change connectedComponentIn (A ∩ cluster μ 1 z t) x ⊆ A'
    rw [← hcomponent]
    exact (connectedComponentIn_subset _ _).trans inter_subset_left
  have hxY : x ∈ Y := mem_connectedComponentIn hx
  have hxA' : x ∈ A' ∩ cluster μ 1 z t := ⟨hYsubA' hxY, hx.2⟩
  have hA'unit : closure A' ⊆ closedBall (0 : ℂ) 1 \ {z} := by
    intro y hy
    refine ⟨closure_minimal (hAin.trans ball_subset_closedBall) isClosed_closedBall
      (closure_mono hA'sub hy), ?_⟩
    intro hyz
    apply hzA'
    simpa only [mem_singleton_iff] using hyz ▸ hy
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ zero_lt_one hV hz ht).1
  have hYopen : IsOpen Y := (hA.inter hcluster).connectedComponentIn
  have hYb : Bornology.IsBounded Y := isBounded_ball.subset
    ((connectedComponentIn_subset _ _).trans (inter_subset_left.trans hAin))
  have happrox' : ∀ (V : Set ℂ), IsOpen V → IsCompact (closure V) →
      closure V ⊆ connectedComponentIn (A' ∩ cluster μ 1 z t) x →
      ∀ ε : ℝ, 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ y ∈ closure V, |(closure A').indicator (fun y => max 0 (odometer μ 1 z t y)) y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
        ∀ y ∈ V, 0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y := by
    intro V hVo hVc hVY ε hε
    have hVY' : closure V ⊆ Y := by
      change closure V ⊆ connectedComponentIn (A ∩ cluster μ 1 z t) x
      simpa only [hcomponent] using hVY
    obtain ⟨f, hf, hfgen⟩ := happrox V hVo hVc hVY' ε hε
    refine ⟨f, ?_, hfgen⟩
    intro y hy
    have hyA' := hYsubA' (hVY' hy)
    have hyunit := hA'unit (subset_closure hyA')
    have hynonneg := odometer_nonneg (μ := μ) ht.le hyunit.1 hyunit.2
    simpa [subset_closure hyA', max_eq_right hynonneg] using hf y hy
  have hsmall := odometer_le_harmonicMeasure_of_compact_local_generator_approximation
    hμ hV hz ht hA'o (hA'sub.trans hAin) hA'unit hxA' happrox'
  rw [hcomponent] at hsmall
  have hBs : (⨆ y ∈ frontier A' ∩ closure Y, odometerExt μ z t y) ≤
      ⨆ y ∈ frontier A ∩ closure Y, odometerExt μ z t y := by
    exact biSup_mono fun y hy => hfront hy
  have hP := harmonicMeasure_mono_of_frontier_subset hA hA'o hYopen hYb hYsubA'
    (hfront.trans inter_subset_left) hxY
  exact hsmall.trans (mul_le_mul' hBs hP)

end HarmonicBalls.Section6
