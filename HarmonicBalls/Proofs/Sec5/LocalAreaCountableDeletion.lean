import HarmonicBalls.Proofs.Sec5.LocalAreaPunctureObstruction
import HarmonicBalls.Proofs.Sec5.CountableDiscInadmissibility

/-! # Local area bounds and countable deletions -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- A relatively closed countable deletion makes the pointwise infimum
inadmissible when the measure has a positive area lower bound near one
interior deleted point. -/
theorem relative_countable_disc_infimum_not_admissible_of_local_area_lower_bound
    {μ : Measure ℂ} (hμloc : IsLocallyFiniteMeasure μ) {R βm βp t C : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (haK : a ∈ K) (ha : a ∈ ball (0 : ℂ) R)
    {V : Set ℂ} (hC : 0 < C) (hopen : IsOpen V) (haV : a ∈ V)
    (hμ : (ENNReal.ofReal C • volume).restrict V ≤ μ) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t := by
  have haz : a ≠ z := fun h => hz.2 (h ▸ haK)
  obtain ⟨w, hw, hn⟩ := exists_disc_supersolution_neg_of_local_area_lower_bound
    hz.1 ha haz ht hC hopen haV hμ
  have hneg : leastSupersolution μ R z t a < 0 :=
    lt_of_le_of_lt (leastSupersolution_le hw (ball_subset_closedBall ha) haz) hn
  intro hadm
  have hzero := (leastSupersolutionOn_relative_countable_disc_mem_iff
    hμloc hR hV K hD hK hz ht).mp hadm a haK ha
  linarith

#print axioms relative_countable_disc_infimum_not_admissible_of_local_area_lower_bound

end HarmonicBalls
