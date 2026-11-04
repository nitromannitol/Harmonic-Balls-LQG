import HarmonicBalls.Proofs.Sec6.TruncatedSubharmonic
import HarmonicBalls.Steps.Sec11.OdometerMaximum
import HarmonicBalls.Proofs.Sec3.OpenLaplacian

/-! # Componentwise odometer truncation

The odometer restricted to a union of components remains subharmonic away
from its pole, as used in the proof of Lemma 6.8.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

/-- Extension by zero on a union of components preserves subharmonicity
when the function is zero outside the original open set. -/
theorem laplacianGE_indicator_of_union_components {U G Λ : Set ℂ} {u : ℂ → ℝ}
    (hU : IsOpen U) (hG : IsOpen G) (hGU : G ⊆ U)
    (hΛG : Λ ⊆ G) (hcomp : ∀ x ∈ Λ, connectedComponentIn G x ⊆ Λ)
    (hcont : ContinuousOn u U) (hnonneg : ∀ x ∈ U, 0 ≤ u x)
    (hzero : ∀ x ∈ U, x ∉ G → u x = 0)
    (hsub : IsSubharmonicOn U u) : LaplacianGE (Λ.indicator u) 0 U := by
  have hΛopen := isOpen_of_union_components hG hΛG hcomp
  have hfront : ∀ x ∈ U ∩ frontier Λ, u x = 0 := by
    intro x hx
    exact hzero x hx.1 (fun hxG => disjoint_left.mp
      (frontier_union_components_disjoint hG hΛG hcomp) hx.2 hxG)
  have hsubΛ : IsSubharmonicOn Λ u := by
    refine ⟨hsub.1.mono (hΛG.trans hGU), fun x hx r hr hball => ?_⟩
    exact hsub.2 x (hGU (hΛG hx)) r hr (hball.trans (hΛG.trans hGU))
  exact laplacianGE_indicator_of_zero_frontier hU hΛopen hcont hnonneg hfront hsubΛ

/-- In any open set away from the pole, the odometer restricted to a union
of components of the cluster has nonnegative distributional Laplacian. -/
theorem odometer_indicator_union_components_laplacianGE
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ) :
    LaplacianGE (Λ.indicator (odometer μ R z t)) 0 U := by
  obtain ⟨hc, hs⟩ := odometer_continuousOn_and_subharmonic hμ hR hV hz ht
  have hcU : ContinuousOn (odometer μ R z t) U := hc.mono hUsub
  have hsU : IsSubharmonicOn U (odometer μ R z t) := by
    refine ⟨hs.1.mono hUsub, fun x hx r hr hball => ?_⟩
    exact hs.2 x (hUsub hx) r hr (hball.trans hUsub)
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hz ht).1
  apply laplacianGE_indicator_of_union_components hU (hU.inter hcluster) inter_subset_left
    hΛsub hcomp hcU (fun x hx => odometer_nonneg ht.le (ball_subset_closedBall (hUsub hx).1) (hUsub hx).2) ?_ hsU
  intro x hx hxG
  have hxnot : x ∉ cluster μ R z t := fun h => hxG ⟨hx, h⟩
  have hnotpos : ¬ 0 < odometer μ R z t x := fun h => hxnot (mem_cluster_iff.mpr ⟨(hUsub hx).1, Or.inr h⟩)
  exact le_antisymm (le_of_not_gt hnotpos)
    (odometer_nonneg ht.le (ball_subset_closedBall (hUsub hx).1) (hUsub hx).2)

end HarmonicBalls.Section6
