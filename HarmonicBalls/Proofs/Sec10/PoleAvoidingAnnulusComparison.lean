import HarmonicBalls.Proofs.Sec10.PuncturedDomainExit
import HarmonicBalls.Proofs.Sec6.AnnulusMassOdometer

/-! # Brownian comparison on an annulus containing the pole -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6 MarkovProcess
open scoped ENNReal

/-- A comparison on domains avoiding the pole extends to a component avoiding
it, by puncturing the annulus. -/
theorem component_annulus_comparison_of_punctured
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    {w : ℂ} {r : ℝ} (hr : 0 < r) (hcontain : closedBall w (5 * r) ⊆ U)
    (hcomparison : ∀ A : Set ℂ, IsOpen A → A ⊆ ball (0 : ℂ) 1 → z ∉ A →
      ∀ x ∈ A ∩ cluster μ 1 z t, ∀ Λx : Set ℂ,
      Λx = connectedComponentIn (A ∩ cluster μ 1 z t) x →
      (⨆ y ∈ frontier A ∩ closure Λx, odometerExt μ z t y) ≠ ⊤ →
      odometerExt μ z t x ≤ (⨆ y ∈ frontier A ∩ closure Λx, odometerExt μ z t y) *
        planarBrownianMotion x {p | ContinuousPath.exitTime A p ≤ hittingTime (A \ Λx) p}) :
    ∀ x ∈ D ∩ sphere w (4 * r), ∃ Y : Set ℂ,
      MeasurableSet Y ∧ Y ⊆ D ∩ annulus w (3 * r) (5 * r) ∧
      odometerExt μ z t x ≤
        (⨆ y ∈ frontier (annulus w (3 * r) (5 * r)) ∩ closure Y, odometerExt μ z t y) *
        planarBrownianMotion x {p | ContinuousPath.exitTime (annulus w (3 * r) (5 * r)) p ≤
          hittingTime (annulus w (3 * r) (5 * r) \ Y) p} := by
  intro x hx
  let A := annulus w (3 * r) (5 * r)
  have hAopen : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAsub : A ⊆ U := sdiff_subset.trans (ball_subset_closedBall.trans hcontain)
  have hxA : x ∈ A := by
    have hxnorm : dist x w = 4 * r := hx.2
    exact ⟨mem_ball.mpr (by linarith), fun h => by have := mem_closedBall.mp h; linarith⟩
  obtain ⟨d, hd, hDd⟩ := hD
  have hDsub : D ⊆ U ∩ cluster μ 1 z t := by
    rw [← hDd]
    exact connectedComponentIn_subset _ _
  have hxcluster := (hDsub hx.1).2
  let Y := connectedComponentIn (A ∩ cluster μ 1 z t) x
  have hxY : x ∈ Y := mem_connectedComponentIn ⟨hxA, hxcluster⟩
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ zero_lt_one hV hz ht).1
  have hYopen : IsOpen Y := (hAopen.inter hcluster).connectedComponentIn
  have hYsub : Y ⊆ D ∩ A := by
    intro y hy
    have hYC : Y ⊆ connectedComponentIn (U ∩ cluster μ 1 z t) x :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn hxY (by
        intro q hq
        exact ⟨hAsub (connectedComponentIn_subset _ _ hq).1,
          (connectedComponentIn_subset _ _ hq).2⟩)
    have hyD : y ∈ D := by
      rw [← hDd] at hx ⊢
      rw [connectedComponentIn_eq hx.1]
      exact hYC hy
    exact ⟨hyD, (connectedComponentIn_subset _ _ hy).1⟩
  have hYAsub : Y ⊆ A := hYsub.trans inter_subset_right
  have hYclball : closure Y ⊆ closedBall w (5 * r) :=
    closure_minimal (hYAsub.trans (sdiff_subset.trans ball_subset_closedBall)) isClosed_closedBall
  have hzYcl : z ∉ closure Y := by
    intro hzY
    exact pole_not_mem_closure_component_in_domain hμ hV hz ht hU ⟨d, hd, hDd⟩ hzD
      (hcontain (hYclball hzY)) (closure_mono (hYsub.trans inter_subset_left) hzY)
  have hKsub : closedBall w (5 * r) ∩ closure D ⊆ ball (0 : ℂ) 1 \ {z} := by
    intro y hy
    refine ⟨hUsub (hcontain hy.1), ?_⟩
    intro hyz
    have hyz' : y = z := by simpa using hyz
    exact pole_not_mem_closure_component_in_domain hμ hV hz ht hU ⟨d, hd, hDd⟩ hzD
      (hyz' ▸ hcontain hy.1) (hyz' ▸ hy.2)
  have hcont := (odometer_continuousOn_and_subharmonic hμ zero_lt_one hV hz ht).1
  obtain ⟨M, hM⟩ := ((isCompact_closedBall w (5 * r)).inter_right isClosed_closure).bddAbove_image
    (hcont.mono hKsub)
  have hfront : frontier A ⊆ closedBall w (5 * r) :=
    frontier_subset_closure.trans (closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall)
  have htop : (⨆ y ∈ frontier A ∩ closure Y, odometerExt μ z t y) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (show _ ≤ ENNReal.ofReal M from ?_) ENNReal.ofReal_lt_top
    refine iSup_le fun y => iSup_le fun hy => ?_
    have hyK : y ∈ closedBall w (5 * r) ∩ closure D :=
      ⟨hfront hy.1, closure_mono (hYsub.trans inter_subset_left) hy.2⟩
    have hyz : y ≠ z := by simpa using (hKsub hyK).2
    simp only [odometerExt, hyz, ↓reduceIte]
    exact ENNReal.ofReal_le_ofReal (hM ⟨y, hyK, rfl⟩)
  have hsup : (⨆ y ∈ frontier (A \ {z}) ∩ closure Y, odometerExt μ z t y) ≤
      ⨆ y ∈ frontier A ∩ closure Y, odometerExt μ z t y :=
    biSup_mono fun y hy => frontier_puncture_inter_closure_subset A Y z hzYcl hy
  have htop' : (⨆ y ∈ frontier (A \ {z}) ∩ closure Y, odometerExt μ z t y) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hsup (lt_top_iff_ne_top.mpr htop))
  have hzY : z ∉ Y := fun h => hzYcl (subset_closure h)
  have hcomp : connectedComponentIn ((A \ {z}) ∩ cluster μ 1 z t) x = Y := by
    have heq : (A \ {z}) ∩ cluster μ 1 z t = (A ∩ cluster μ 1 z t) \ {z} := by ext q; simp; tauto
    rw [heq]
    exact connectedComponentIn_sdiff_singleton_eq ⟨hxA, hxcluster⟩ hzY
  have hxAz : x ∈ A \ {z} := ⟨hxA, by simpa using (fun e : x = z => hzY (e ▸ hxY))⟩
  refine ⟨Y, hYopen.measurableSet, hYsub, ?_⟩
  have hc := hcomparison (A \ {z}) (hAopen.sdiff isClosed_singleton)
    (sdiff_subset.trans (hAsub.trans hUsub)) (by simp) x ⟨hxAz, hxcluster⟩ Y hcomp.symm htop'
  rw [planarBrownianMotion_exit_puncture_eq hAopen hYopen hYAsub hzYcl hxY] at hc
  exact hc.trans (mul_le_mul' hsup le_rfl)

/-- Lemma 6.9 implies good-annulus decay for components which avoid the pole,
even when the surrounding annulus contains it. -/
theorem component_goodAnnulus_decay_of_punctured_comparison
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    {w : ℂ} {r a b : ℝ} (hr : 0 < r) (hcontain : closedBall w (5 * r) ⊆ U)
    (hgood : IsGoodAnnulus μ r w a b)
    (hmass : μ (D ∩ annulus w (3 * r) (5 * r)) ≤
      ENNReal.ofReal a * μ (annulus w (3 * r) (5 * r)))
    (hcomparison : ∀ A : Set ℂ, IsOpen A → A ⊆ ball (0 : ℂ) 1 → z ∉ A →
      ∀ x ∈ A ∩ cluster μ 1 z t, ∀ Λx : Set ℂ,
      Λx = connectedComponentIn (A ∩ cluster μ 1 z t) x →
      (⨆ y ∈ frontier A ∩ closure Λx, odometerExt μ z t y) ≠ ⊤ →
      odometerExt μ z t x ≤ (⨆ y ∈ frontier A ∩ closure Λx, odometerExt μ z t y) *
        planarBrownianMotion x {p | ContinuousPath.exitTime A p ≤ hittingTime (A \ Λx) p}) :
    (⨆ x ∈ D ∩ ball w (4 * r), odometerExt μ z t x) ≤
      ENNReal.ofReal b * ⨆ x ∈ D ∩ annulus w (3 * r) (5 * r), odometerExt μ z t x := by
  apply component_goodAnnulus_decay_of_harmonic_comparisons hμ hV hz ht hU hUsub hD hzD hr hcontain hgood hmass
  exact component_annulus_comparison_of_punctured hμ hV hz ht hU hUsub hD hzD hr hcontain hcomparison

end HarmonicBalls
