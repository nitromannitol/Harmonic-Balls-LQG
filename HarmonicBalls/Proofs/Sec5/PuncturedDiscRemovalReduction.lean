import HarmonicBalls.Proofs.Sec5.PuncturedDiscInadmissibility

/-! # Reduction of punctured-disc comparison to point removal

The only additional analytic step used below is removal of the puncture from
the distributional Laplacian inequality for each punctured-domain competitor.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- The closure of a disc is unchanged by deleting an interior point. -/
theorem closure_punctured_disc {R : ℝ} {a : ℂ} (ha : a ∈ ball (0 : ℂ) R) :
    closure (ball (0 : ℂ) R \ {a}) = closedBall 0 R := by
  have hR : 0 < R := (norm_nonneg a).trans_lt (mem_ball_zero_iff.mp ha)
  apply Subset.antisymm
  · exact closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall
  · rw [← closure_ball 0 hR.ne']
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_cases hxa : x = a
    · subst x
      have h := (dense_compl_singleton a).open_subset_closure_inter isOpen_ball ha
      simpa [sdiff_eq, inter_comm] using h
    · exact subset_closure ⟨hx, by simpa using hxa⟩

/-- If its distributional Laplacian inequality extends across the puncture,
a punctured-disc supersolution is also a full-disc supersolution. -/
theorem punctured_disc_supersolution_mem_disc_of_laplacianLE
    {μ : Measure ℂ} {R t : ℝ} {z a : ℂ} {w : ℂ → ℝ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 ≤ t) (hw : w ∈ supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t)
    (hΔ : LaplacianLE w μ (ball 0 R)) : w ∈ supersolutions μ R z t := by
  have hclosure := closure_punctured_disc ha
  refine ⟨by simpa only [hclosure] using hw.1, hΔ, ?_⟩
  intro x hx hxz
  have hxcl : x ∈ closure (ball (0 : ℂ) R \ {a}) := hclosure ▸ hx
  have hwx := hw.2.2 x hxcl hxz
  by_cases hxa : x = a
  · subst x
    have haU : a ∉ ball (0 : ℂ) R \ {a} := by simp
    rw [greenFunction_of_notMem_right haU, mul_zero] at hwx
    have hG : 0 ≤ greenFunction (ball (0 : ℂ) R) z a :=
      greenFunction_nonneg isBounded_ball z a
    nlinarith
  · by_cases hxU : x ∈ ball (0 : ℂ) R
    · rw [greenFunction_punctured_ball ha hz ⟨hxU, by simpa using hxa⟩ hxz] at hwx
      exact hwx
    · have hxU' : x ∉ ball (0 : ℂ) R \ {a} := fun h => hxU h.1
      rw [greenFunction_of_notMem_right hxU'] at hwx
      rw [greenFunction_of_notMem_right hxU]
      exact hwx

/-- Point removal for all competitors yields equality of the two infima away
from the puncture and pole. The point-removal premise is explicit. -/
theorem leastSupersolutionOn_punctured_disc_eq_of_point_removal
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a x : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 < t) (hx : x ∈ ball (0 : ℂ) R \ {a}) (hxz : x ≠ z)
    (hremove : ∀ w ∈ supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t,
      LaplacianLE w μ (ball 0 R)) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t x =
      leastSupersolution μ R z t x := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  apply le_antisymm
  · exact leastSupersolutionOn_punctured_disc_le_supersolution ha hz hw hx hxz
  · apply le_csInf
    · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (isBounded_ball.subset sdiff_subset) ht.le, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact leastSupersolution_le
        (punctured_disc_supersolution_mem_disc_of_laplacianLE ha hz ht.le hw (hremove w hw))
        (ball_subset_closedBall hx.1) hxz

/-- Under point removal, deleting the puncture deletes exactly that point
from the full-disc cluster. -/
theorem clusterOn_punctured_disc_eq_sdiff_of_point_removal
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t)
    (hremove : ∀ w ∈ supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t,
      LaplacianLE w μ (ball 0 R)) :
    clusterOn μ (ball (0 : ℂ) R \ {a}) z t = cluster μ R z t \ {a} := by
  ext x
  simp only [clusterOn, cluster, mem_ofPred_eq, mem_sdiff, mem_singleton_iff]
  by_cases hxa : x = a
  · subst x
    simp
  · by_cases hx : x ∈ ball (0 : ℂ) R
    · have hxU : x ∈ ball (0 : ℂ) R \ {a} := ⟨hx, by simpa using hxa⟩
      by_cases hxz : x = z
      · simp only [hxz, true_or, and_true]
      · have hG := greenFunction_punctured_ball ha hz hxU hxz
        have hv := leastSupersolutionOn_punctured_disc_eq_of_point_removal
          hμ hR hV ha hz ht hxU hxz hremove
        simp only [hx, hxa, hxz, hG, hv, false_or, true_and, and_true,
          not_false_eq_true]
    · have hxU : x ∉ ball (0 : ℂ) R \ {a} := fun h => hx h.1
      simp only [hx, false_and]

#print axioms closure_punctured_disc
#print axioms punctured_disc_supersolution_mem_disc_of_laplacianLE
#print axioms leastSupersolutionOn_punctured_disc_eq_of_point_removal
#print axioms clusterOn_punctured_disc_eq_sdiff_of_point_removal

end HarmonicBalls
