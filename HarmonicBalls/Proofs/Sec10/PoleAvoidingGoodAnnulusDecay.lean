import HarmonicBalls.Proofs.Sec10.PoleAvoidingBoundarySup
import MarkovProcess.Path.Exhaustion

/-! # Good-annulus decay for pole-avoiding components -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6 MarkovProcess
open scoped ENNReal

/-- Staying in `Y` until exit from `A` is exactly avoiding `A \ Y` until
exit from `A`. The identity is pathwise and needs no regularity of the sets. -/
theorem exitTime_le_exitTime_iff_le_hittingTime_sdiff
    {A Y : Set ℂ} (p : ContinuousPath ℂ) :
    ContinuousPath.exitTime A p ≤ ContinuousPath.exitTime Y p ↔
      ContinuousPath.exitTime A p ≤ hittingTime (A \ Y) p := by
  constructor
  · intro h
    apply h.trans (ContinuousPath.exitTime_mono ?_ p)
    intro x hx hx'
    exact hx'.2 hx
  · intro h
    apply (ContinuousPath.le_exitTime_iff Y p _).2
    intro v hv
    by_cases hvA : p v ∈ A
    · exact h.trans (ContinuousPath.exitTime_le_of_notMem (A \ Y)ᶜ p v
        (by simpa using (show p v ∈ A \ Y from ⟨hvA, hv⟩)))
    · exact ContinuousPath.exitTime_le_of_notMem A p v hvA

/-- In a good annulus the probability appearing in the odometer comparison is
at most the good-annulus parameter. -/
theorem IsGoodAnnulus.hitting_sdiff_probability_le
    {μ : Measure ℂ} {r : ℝ} {w : ℂ} {a b : ℝ}
    (hgood : IsGoodAnnulus μ r w a b) {Y : Set ℂ} (hYmeas : MeasurableSet Y)
    (hYA : Y ⊆ annulus w (3 * r) (5 * r))
    (hmass : μ Y ≤ ENNReal.ofReal a * μ (annulus w (3 * r) (5 * r)))
    {x : ℂ} (hx : x ∈ sphere w (4 * r)) :
    planarBrownianMotion x
      {p | ContinuousPath.exitTime (annulus w (3 * r) (5 * r)) p ≤
        hittingTime (annulus w (3 * r) (5 * r) \ Y) p} ≤ ENNReal.ofReal b := by
  have heq : {p : ContinuousPath ℂ |
      ContinuousPath.exitTime (annulus w (3 * r) (5 * r)) p ≤
        hittingTime (annulus w (3 * r) (5 * r) \ Y) p} =
      {p | ContinuousPath.exitTime (annulus w (3 * r) (5 * r)) p ≤
        ContinuousPath.exitTime Y p} := by
    ext p
    exact (exitTime_le_exitTime_iff_le_hittingTime_sdiff p).symm
  rw [heq]
  exact hgood Y hYmeas hYA hmass x hx

/-- Good-annulus decay follows from pointwise Brownian odometer comparisons
for the relevant annular subsets of a pole-avoiding component. -/
theorem component_goodAnnulus_decay_of_harmonic_comparisons
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    {w : ℂ} {r a b : ℝ} (hr : 0 < r)
    (hcontain : closedBall w (5 * r) ⊆ U)
    (hgood : IsGoodAnnulus μ r w a b)
    (hmass : μ (D ∩ annulus w (3 * r) (5 * r)) ≤
      ENNReal.ofReal a * μ (annulus w (3 * r) (5 * r)))
    (hcomp : ∀ x ∈ D ∩ sphere w (4 * r), ∃ Y : Set ℂ,
      MeasurableSet Y ∧ Y ⊆ D ∩ annulus w (3 * r) (5 * r) ∧
      odometerExt μ z t x ≤
        (⨆ y ∈ frontier (annulus w (3 * r) (5 * r)) ∩ closure Y,
          odometerExt μ z t y) *
        planarBrownianMotion x
          {p | ContinuousPath.exitTime (annulus w (3 * r) (5 * r)) p ≤
            hittingTime (annulus w (3 * r) (5 * r) \ Y) p}) :
    (⨆ x ∈ D ∩ ball w (4 * r), odometerExt μ z t x) ≤
      ENNReal.ofReal b * ⨆ x ∈ D ∩ annulus w (3 * r) (5 * r), odometerExt μ z t x := by
  have hfront : frontier (annulus w (3 * r) (5 * r)) ⊆ U := by
    apply frontier_subset_closure.trans
    apply (closure_minimal ?_ isClosed_closedBall).trans hcontain
    exact sdiff_subset.trans ball_subset_closedBall
  have hdisc : closedBall w (4 * r) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans hcontain
  apply component_odometer_iSup_ball_le_of_sphere_bound hμ hV hz ht hU hUsub hD hzD
    (by positivity) hdisc
  intro x hx
  obtain ⟨Y, hmeas, hY, hcompare⟩ := hcomp x hx
  have hprob := hgood.hitting_sdiff_probability_le hmeas (hY.trans inter_subset_right)
    ((measure_mono hY).trans hmass) hx.2
  have hsup : (⨆ y ∈ frontier (annulus w (3 * r) (5 * r)) ∩ closure Y,
      odometerExt μ z t y) ≤
      ⨆ y ∈ D ∩ annulus w (3 * r) (5 * r), odometerExt μ z t y := by
    apply (biSup_mono fun y hy => (show y ∈ U ∩ closure Y from ⟨hfront hy.1, hy.2⟩)).trans
    exact odometerExt_iSup_closure_le_iSup_inter_of_pole_not_mem
      hμ hV hz ht hU hUsub hD hzD hY
  calc odometerExt μ z t x ≤ _ := hcompare
    _ ≤ (⨆ y ∈ D ∩ annulus w (3 * r) (5 * r), odometerExt μ z t y) * ENNReal.ofReal b :=
      mul_le_mul' hsup hprob
    _ = _ := mul_comm _ _

end HarmonicBalls
