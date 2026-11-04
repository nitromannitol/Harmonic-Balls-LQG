import HarmonicBalls.Proofs.Sec5.FinitePunctureCompetitors
import HarmonicBalls.Proofs.Sec5.PuncturedDiscStrongCompatibility

/-! # Strong compatibility for finitely punctured discs -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- At a deleted point, the punctured infimum tends to the full-disc least
supersolution along the punctured disc. -/
theorem tendsto_leastSupersolutionOn_finset_punctured_disc_at_puncture
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R) (ha : a ∈ K)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t) :
    Tendsto (leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t)
      (𝓝[ball (0 : ℂ) R \ (K : Set ℂ)] a) (𝓝 (leastSupersolution μ R z t a)) := by
  obtain ⟨_, hcont, _⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hfull : Tendsto (leastSupersolution μ R z t)
      (𝓝[ball (0 : ℂ) R \ (K : Set ℂ)] a) (𝓝 (leastSupersolution μ R z t a)) :=
    (hcont a (ball_subset_closedBall (hK ha))).mono (sdiff_subset.trans ball_subset_closedBall)
  apply hfull.congr'
  have haz : a ≠ z := fun h => hz.2 (h ▸ ha)
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ x in 𝓝 a, x ≠ z from isOpen_compl_singleton.mem_nhds haz).filter_mono
      (nhdsWithin_le_nhds : 𝓝[ball (0 : ℂ) R \ (K : Set ℂ)] a ≤ 𝓝 a)] with x hx hxz
  exact (leastSupersolutionOn_finset_punctured_disc_eq hμ hR hV K hK hz ht hx hxz).symm

/-- The punctured infimum is continuous at a deleted point exactly when the
full-disc least supersolution vanishes there. -/
theorem continuousWithinAt_finset_punctured_infimum_iff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R) (ha : a ∈ K)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t) :
    ContinuousWithinAt (leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t)
        (ball (0 : ℂ) R \ (K : Set ℂ)) a ↔ leastSupersolution μ R z t a = 0 := by
  have hac : a ∈ closure (ball (0 : ℂ) R \ (K : Set ℂ)) := by
    rw [closure_sdiff_finset_of_isOpen isOpen_ball, closure_ball 0 hR.ne']
    exact ball_subset_closedBall (hK ha)
  have : (𝓝[ball (0 : ℂ) R \ (K : Set ℂ)] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hac
  have haz : a ≠ z := fun h => hz.2 (h ▸ ha)
  have hzero := leastSupersolutionOn_eq_zero_of_boundary
    (μ := μ) (isBounded_ball.subset sdiff_subset) ht.le hac (by simp [ha]) haz
  have hlim := tendsto_leastSupersolutionOn_finset_punctured_disc_at_puncture hμ hR hV K hK ha hz ht
  constructor
  · intro hc
    exact (tendsto_nhds_unique hlim hc).trans hzero
  · intro h
    change Tendsto _ _ (𝓝 (leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t a))
    simpa [h, hzero] using hlim

/-- Admissibility forces the full-disc least supersolution to vanish at every
removed point. -/
theorem leastSupersolution_eq_zero_of_finset_punctured_admissible
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    (hadm : leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) :
    ∀ a ∈ K, leastSupersolution μ R z t a = 0 := by
  intro a ha
  have hac : a ∈ closure (ball (0 : ℂ) R \ (K : Set ℂ)) := by
    rw [closure_sdiff_finset_of_isOpen isOpen_ball, closure_ball 0 hR.ne']
    exact ball_subset_closedBall (hK ha)
  exact (continuousWithinAt_finset_punctured_infimum_iff hμ hR hV K hK ha hz ht).mp
    ((hadm.1 a hac).mono subset_closure)

/-- The cluster closures agree without requiring admissibility of the
punctured-domain infimum. -/
theorem closure_clusterOn_finset_punctured_disc_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t) :
    closure (clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) = closure (cluster μ R z t) := by
  rw [clusterOn_finset_punctured_disc_eq_sdiff hμ hR hV K hK hz ht]
  apply closure_sdiff_finset_of_isOpen
  rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz.1 t ht).2.2.1]
  exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hμ hR hV hz.1 ht

/-- Strong compatibility when the ambient disc represents the regularized
family at the specified time. -/
theorem regularizedFamily_closure_eq_clusterOn_finset_punctured_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R) :
    closure (Λ t) = closure (clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) := by
  have heq := hΛ.2.2 t ht R hR hcl R le_rfl
  have hopen : IsOpen (cluster μ R z t) := by
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz.1 t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hμ hR hV hz.1 ht
  rw [heq, closure_regularizedCluster_eq_of_isOpen hopen,
    closure_clusterOn_finset_punctured_disc_eq hμ hR hV K hK hz ht]

/-- Both compact-containment alternatives imply strong compatibility for a
finitely punctured disc. -/
theorem regularizedFamily_strongCompatibility_finset_punctured_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ (K : Set ℂ) ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) ⊆ ball 0 R \ (K : Set ℂ)) :
    closure (Λ t) = closure (clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) := by
  rcases hcl with hΛcl | hcl
  · exact regularizedFamily_closure_eq_clusterOn_finset_punctured_disc hμ hR (hV R hR)
      K hK hz ht hΛ (hΛcl.trans sdiff_subset)
  · have hc := closure_clusterOn_finset_punctured_disc_eq hμ hR (hV R hR) K hK hz ht
    have hdisc : closure (cluster μ R z t) ⊆ ball (0 : ℂ) R := by
      rw [← hc]
      exact hcl.trans sdiff_subset
    have hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t) := by
      intro r hr hzr
      rw [(obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr (hV r hr) z hzr t ht).2.2.1]
      exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
        hμ hr (hV r hr) hzr ht
    have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ hR (hV R hR) hz.1 ht).2.2
    rw [hc]
    exact regularizedFamily_closure_eq_discCluster_of_compact_containment
      hR hz.1 ht hΛ hopen hv hdisc

#print axioms tendsto_leastSupersolutionOn_finset_punctured_disc_at_puncture
#print axioms continuousWithinAt_finset_punctured_infimum_iff
#print axioms leastSupersolution_eq_zero_of_finset_punctured_admissible
#print axioms closure_clusterOn_finset_punctured_disc_eq
#print axioms regularizedFamily_closure_eq_clusterOn_finset_punctured_disc
#print axioms regularizedFamily_strongCompatibility_finset_punctured_disc

end HarmonicBalls
