import HarmonicBalls.Proofs.Sec5.PuncturedDiscInadmissibility

/-! # The infimum near an inactive puncture

Where the disc obstacle is active, the punctured-domain infimum agrees with
that obstacle. This gives its one-sided limit at an inactive puncture.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- Away from the disc cluster, the punctured-disc infimum equals the obstacle. -/
theorem leastSupersolutionOn_punctured_disc_eq_obstacle_of_not_mem_cluster
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a x : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 < t) (hx : x ∈ ball (0 : ℂ) R \ {a}) (hxz : x ≠ z)
    (hnot : x ∉ cluster μ R z t) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t x =
      -t * greenFunction (ball (0 : ℂ) R \ {a}) z x := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hupper := leastSupersolutionOn_punctured_disc_le_supersolution ha hz hw hx hxz
  have heq := odometer_eq_zero_of_notMem_cluster (le_of_lt ht) hx.1 hnot
  have hG := greenFunction_punctured_ball ha hz hx hxz
  have hlower : -t * greenFunction (ball (0 : ℂ) R \ {a}) z x ≤
      leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t x := by
    apply le_csInf
    · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (isBounded_ball.subset sdiff_subset) ht.le, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2.2 x (subset_closure hx) hxz
  change leastSupersolution μ R z t x + t * greenFunction (ball 0 R) z x = 0 at heq
  rw [hG] at hlower ⊢
  linarith

/-- If the puncture lies outside the disc cluster, the punctured-domain
infimum approaches the negative full-disc Green obstacle, including when the
puncture lies on the cluster boundary. -/
theorem tendsto_leastSupersolutionOn_punctured_disc_at_inactive_puncture
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 < t) (hnot : a ∉ cluster μ R z t) :
    Tendsto (leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t)
      (𝓝[ball (0 : ℂ) R \ {a}] a) (𝓝 (-t * greenFunction (ball 0 R) z a)) := by
  obtain ⟨_, hcont, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hv0 := odometer_eq_zero_of_notMem_cluster ht.le ha hnot
  have hval : leastSupersolution μ R z t a = -t * greenFunction (ball 0 R) z a := by
    change leastSupersolution μ R z t a + t * greenFunction (ball 0 R) z a = 0 at hv0
    linarith
  have hupper : Tendsto (leastSupersolution μ R z t)
      (𝓝[ball (0 : ℂ) R \ {a}] a) (𝓝 (-t * greenFunction (ball 0 R) z a)) := by
    rw [← hval]
    exact ((hcont a (ball_subset_closedBall ha)).mono
      (sdiff_subset.trans ball_subset_closedBall))
  have hlower := (tendsto_greenFunction_punctured_ball_at_puncture ha hz).const_mul (-t)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · have haz : a ≠ z := Ne.symm (show z ≠ a by simpa using hz.2)
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ x in 𝓝 a, x ≠ z from isOpen_compl_singleton.mem_nhds haz).filter_mono
        (nhdsWithin_le_nhds : 𝓝[ball (0 : ℂ) R \ {a}] a ≤ 𝓝 a)] with x hx hxz
    apply le_csInf
    · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (isBounded_ball.subset sdiff_subset) ht.le, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2.2 x (subset_closure hx) hxz
  · have haz : a ≠ z := Ne.symm (show z ≠ a by simpa using hz.2)
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ x in 𝓝 a, x ≠ z from isOpen_compl_singleton.mem_nhds haz).filter_mono
        (nhdsWithin_le_nhds : 𝓝[ball (0 : ℂ) R \ {a}] a ≤ 𝓝 a)] with x hx hxz
    exact leastSupersolutionOn_punctured_disc_le_supersolution ha hz hw hx hxz

end HarmonicBalls
