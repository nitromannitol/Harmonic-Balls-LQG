import HarmonicBalls.Proofs.Sec5.FinitePointRemoval
import HarmonicBalls.Proofs.Sec6.GreenIntegrability
import Mathlib.Topology.Algebra.Module.Cardinality

/-! # Comparison of supersolutions after finitely many points are removed -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- Removing finitely many points does not change the closure of an open set. -/
theorem closure_sdiff_finset_of_isOpen {U : Set ℂ} (hU : IsOpen U) (K : Finset ℂ) :
    closure (U \ (K : Set ℂ)) = closure U := by
  apply Subset.antisymm (closure_mono sdiff_subset)
  apply closure_minimal _ isClosed_closure
  intro x hx
  have hd : Dense ((K : Set ℂ)ᶜ) := K.finite_toSet.countable.dense_compl ℂ
  have h := hd.open_subset_closure_inter hU hx
  simpa [sdiff_eq, inter_comm] using h

/-- A supersolution on a finitely punctured disc is a supersolution on the
whole disc. Green-function domain monotonicity compares the obstacles. -/
theorem finite_punctured_disc_supersolution_mem_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    (K : Finset ℂ) {z : ℂ} {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) :
    w ∈ supersolutions μ R z t := by
  have hcl : closure (ball (0 : ℂ) R \ (K : Set ℂ)) = closedBall 0 R := by
    rw [closure_sdiff_finset_of_isOpen isOpen_ball, closure_ball 0 hR.ne']
  refine ⟨by simpa only [hcl] using hw.1, ?_, ?_⟩
  · exact laplacianLE_disc_of_finite_removal hμ hR hV
      (hw.1.mono (by rw [hcl]; exact ball_subset_closedBall)) K hw.2.1
  · intro x hx hxz
    have hwx := hw.2.2 x (hcl ▸ hx) hxz
    have hG := Section6.greenFunction_le_of_subset
      (show ball (0 : ℂ) R \ (K : Set ℂ) ⊆ ball 0 R from sdiff_subset)
      isBounded_ball z x
    nlinarith

/-- The full-disc least supersolution is a lower bound for the infimum over
supersolutions on the finitely punctured disc. -/
theorem leastSupersolution_le_finite_punctured_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    (K : Finset ℂ) {z x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    leastSupersolution μ R z t x ≤
      leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t x := by
  apply le_csInf
  · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (isBounded_ball.subset sdiff_subset) ht, rfl⟩⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact leastSupersolution_le
      (finite_punctured_disc_supersolution_mem_disc hμ hR hV ht K hw) hx hxz

/-- A point remains in the punctured cluster if its full-disc odometer
exceeds the obstacle change caused by the Green-function gap. -/
theorem mem_clusterOn_finite_punctured_disc_of_green_gap
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    (K : Finset ℂ) {z x : ℂ} (hx : x ∈ ball (0 : ℂ) R \ (K : Set ℂ))
    (hxz : x ≠ z)
    (hgap : t * (greenFunction (ball 0 R) z x -
      greenFunction (ball (0 : ℂ) R \ (K : Set ℂ)) z x) < odometer μ R z t x) :
    x ∈ clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t := by
  refine ⟨hx, Or.inr ?_⟩
  have hle := leastSupersolution_le_finite_punctured_disc hμ hR hV ht K
    (ball_subset_closedBall hx.1) hxz
  dsimp only [odometer] at hgap
  nlinarith

/-- Equality of the Green functions implies one inclusion of the punctured
cluster comparison. -/
theorem disc_cluster_sdiff_subset_finite_punctured_of_green_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    (K : Finset ℂ) {z : ℂ}
    (hG : ∀ x ∈ ball (0 : ℂ) R \ (K : Set ℂ), x ≠ z →
      greenFunction (ball (0 : ℂ) R \ (K : Set ℂ)) z x =
        greenFunction (ball 0 R) z x) :
    cluster μ R z t \ (K : Set ℂ) ⊆
      clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t := by
  intro x ⟨⟨hxb, hxcluster⟩, hxK⟩
  have hx : x ∈ ball (0 : ℂ) R \ (K : Set ℂ) := ⟨hxb, hxK⟩
  rcases hxcluster with hxz | hxcluster
  · exact ⟨hx, Or.inl hxz⟩
  · by_cases hxz : x = z
    · exact ⟨hx, Or.inl hxz⟩
    · apply mem_clusterOn_finite_punctured_disc_of_green_gap hμ hR hV ht K hx hxz
      rw [hG x hx hxz]
      dsimp only [odometer]
      linarith

#print axioms closure_sdiff_finset_of_isOpen
#print axioms finite_punctured_disc_supersolution_mem_disc
#print axioms leastSupersolution_le_finite_punctured_disc
#print axioms mem_clusterOn_finite_punctured_disc_of_green_gap
#print axioms disc_cluster_sdiff_subset_finite_punctured_of_green_eq

end HarmonicBalls
