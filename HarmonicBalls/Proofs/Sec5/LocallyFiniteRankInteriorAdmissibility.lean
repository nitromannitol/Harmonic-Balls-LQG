import HarmonicBalls.Proofs.Sec5.LocallyFiniteRankAdmissibility

/-! # Interior punctures with locally finite accumulation rank -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- At a deleted point, the punctured infimum tends to the full-disc least
supersolution along the punctured disc. -/
theorem tendsto_leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_at_interior_puncture
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (haR : a ∈ ball (0 : ℂ) R) (ha : a ∈ K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    Tendsto (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t)
      (𝓝[ball (0 : ℂ) R \ K] a) (𝓝 (leastSupersolution μ R z t a)) := by
  obtain ⟨_, hcont, _⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hfull : Tendsto (leastSupersolution μ R z t)
      (𝓝[ball (0 : ℂ) R \ K] a) (𝓝 (leastSupersolution μ R z t a)) :=
    (hcont a (ball_subset_closedBall haR)).mono (sdiff_subset.trans ball_subset_closedBall)
  apply hfull.congr'
  have haz : a ≠ z := fun h => hz.2 (h ▸ ha)
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ x in 𝓝 a, x ≠ z from isOpen_compl_singleton.mem_nhds haz).filter_mono
      (nhdsWithin_le_nhds : 𝓝[ball (0 : ℂ) R \ K] a ≤ 𝓝 a)] with x hx hxz
  exact (leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_eq hμ hR hV hKclosed hK hz ht hx hxz).symm

/-- The punctured infimum is continuous at a deleted point exactly when the
full-disc least supersolution vanishes there. -/
theorem continuousWithinAt_locallyFiniteRankOn_punctured_infimum_at_interior_iff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (haR : a ∈ ball (0 : ℂ) R) (ha : a ∈ K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    ContinuousWithinAt (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t)
        (ball (0 : ℂ) R \ K) a ↔ leastSupersolution μ R z t a = 0 := by
  have hac : a ∈ closure (ball (0 : ℂ) R \ K) := by
    rw [closure_sdiff_countable_inter isOpen_ball
      (countable_inter_open_of_locallyFiniteRankOn isOpen_ball hK),
      closure_ball (0 : ℂ) hR.ne']
    exact ball_subset_closedBall haR
  have : (𝓝[ball (0 : ℂ) R \ K] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hac
  have haz : a ≠ z := fun h => hz.2 (h ▸ ha)
  have hzero := leastSupersolutionOn_eq_zero_of_boundary
    (μ := μ) (isBounded_ball.subset sdiff_subset) ht.le hac (by simp [ha]) haz
  have hlim := tendsto_leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_at_interior_puncture hμ hR hV K hKclosed hK haR ha hz ht
  constructor
  · intro hc
    exact (tendsto_nhds_unique hlim hc).trans hzero
  · intro h
    change Tendsto _ _ (𝓝 (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t a))
    simpa [h, hzero] using hlim

/-- A nonzero full-disc value at an interior deleted point prevents the
punctured infimum from being a supersolution. -/
theorem not_mem_supersolutionsOn_of_locallyFiniteRankOn_interior_puncture
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (haR : a ∈ ball (0 : ℂ) R) (ha : a ∈ K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hneq : leastSupersolution μ R z t a ≠ 0) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t := by
  intro hadm
  have hac : a ∈ closure (ball (0 : ℂ) R \ K) := by
    rw [closure_sdiff_countable_inter isOpen_ball
      (countable_inter_open_of_locallyFiniteRankOn isOpen_ball hK),
      closure_ball (0 : ℂ) hR.ne']
    exact ball_subset_closedBall haR
  exact hneq ((continuousWithinAt_locallyFiniteRankOn_punctured_infimum_at_interior_iff
    hμ hR hV K hKclosed hK haR ha hz ht).mp ((hadm.1 a hac).mono subset_closure))

#print axioms continuousWithinAt_locallyFiniteRankOn_punctured_infimum_at_interior_iff
#print axioms not_mem_supersolutionsOn_of_locallyFiniteRankOn_interior_puncture

end HarmonicBalls
