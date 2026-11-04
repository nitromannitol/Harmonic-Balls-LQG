import HarmonicBalls.Proofs.Sec5.ContinuousPointRemoval
import HarmonicBalls.Proofs.Sec5.IrregularLeastSupersolution
import HarmonicBalls.Proofs.Sec5.CompactFamilyMeasureLocality
import HarmonicBalls.Proofs.Sec5.RestrictedContainmentTest

/-! # Strong compatibility for a punctured disc

Continuous point removal yields both an exact limit of the least
supersolution at the puncture and equality of cluster closures.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- The punctured-disc infimum converges to the full-disc least supersolution
at the removed point, regardless of whether that point lies in the cluster. -/
theorem tendsto_leastSupersolutionOn_punctured_disc_at_puncture
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t) :
    Tendsto (leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t)
      (𝓝[ball (0 : ℂ) R \ {a}] a) (𝓝 (leastSupersolution μ R z t a)) := by
  obtain ⟨_, hcont, _⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hfull : Tendsto (leastSupersolution μ R z t)
      (𝓝[ball (0 : ℂ) R \ {a}] a) (𝓝 (leastSupersolution μ R z t a)) :=
    (hcont a (ball_subset_closedBall ha)).mono (sdiff_subset.trans ball_subset_closedBall)
  apply hfull.congr'
  have haz : a ≠ z := Ne.symm (by simpa using hz.2)
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ x in 𝓝 a, x ≠ z from isOpen_compl_singleton.mem_nhds haz).filter_mono
      (nhdsWithin_le_nhds : 𝓝[ball (0 : ℂ) R \ {a}] a ≤ 𝓝 a)] with x hx hxz
  exact (leastSupersolutionOn_punctured_disc_eq hμ hR hV ha hz ht hx hxz).symm

/-- The punctured infimum is continuous at the removed point precisely when
the full-disc least supersolution vanishes there. -/
theorem continuousWithinAt_punctured_infimum_iff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t) :
    ContinuousWithinAt (leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t)
        (ball (0 : ℂ) R \ {a}) a ↔ leastSupersolution μ R z t a = 0 := by
  have hac : a ∈ closure (ball (0 : ℂ) R \ {a}) := by
    rw [closure_punctured_disc ha]
    exact ball_subset_closedBall ha
  have : (𝓝[ball (0 : ℂ) R \ {a}] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hac
  have haz : a ≠ z := Ne.symm (by simpa using hz.2)
  have hzero := leastSupersolutionOn_eq_zero_of_boundary
    (μ := μ) (isBounded_ball.subset sdiff_subset) ht.le hac (by simp) haz
  have hlim := tendsto_leastSupersolutionOn_punctured_disc_at_puncture hμ hR hV ha hz ht
  constructor
  · intro hc
    exact (tendsto_nhds_unique hlim hc).trans hzero
  · intro h
    change Tendsto _ _ (𝓝 (leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t a))
    simpa [h, hzero] using hlim

/-- Admissibility of the punctured infimum forces the full-disc least
supersolution to vanish at the puncture. -/
theorem leastSupersolution_eq_zero_of_punctured_admissible
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t)
    (hadm : leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t) :
    leastSupersolution μ R z t a = 0 := by
  have hac : a ∈ closure (ball (0 : ℂ) R \ {a}) := by
    rw [closure_punctured_disc ha]
    exact ball_subset_closedBall ha
  exact (continuousWithinAt_punctured_infimum_iff hμ hR hV ha hz ht).mp
    ((hadm.1 a hac).mono subset_closure)

/-- Removing a singleton from an open subset of the plane does not change its closure. -/
theorem closure_sdiff_singleton_of_isOpen {S : Set ℂ} (hS : IsOpen S) (a : ℂ) :
    closure (S \ {a}) = closure S := by
  apply Subset.antisymm (closure_mono sdiff_subset)
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_cases hxa : x = a
  · subst x
    have h := (dense_compl_singleton a).open_subset_closure_inter hS hx
    simpa [sdiff_eq, inter_comm] using h
  · exact subset_closure ⟨hx, by simpa using hxa⟩

/-- Disc and punctured-disc clusters have the same closure without an
admissibility assumption on the punctured least supersolution. -/
theorem closure_clusterOn_punctured_disc_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t) :
    closure (clusterOn μ (ball (0 : ℂ) R \ {a}) z t) = closure (cluster μ R z t) := by
  rw [clusterOn_punctured_disc_eq_sdiff hμ hR hV ha hz ht]
  apply closure_sdiff_singleton_of_isOpen
  rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz.1 t ht).2.2.1]
  exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hμ hR hV hz.1 ht

/-- Strong compatibility for a punctured disc, whenever the regularized
family is represented by the ambient disc. -/
theorem regularizedFamily_closure_eq_clusterOn_punctured_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R) :
    closure (Λ t) = closure (clusterOn μ (ball (0 : ℂ) R \ {a}) z t) := by
  have heq := hΛ.2.2 t ht R hR hcl R le_rfl
  have hopen : IsOpen (cluster μ R z t) := by
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz.1 t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hμ hR hV hz.1 ht
  rw [heq, closure_regularizedCluster_eq_of_isOpen hopen,
    closure_clusterOn_punctured_disc_eq hμ hR hV ha hz ht]

/-- The two compact-containment alternatives in strong compatibility hold
for a punctured disc without punctured-supersolution admissibility. -/
theorem regularizedFamily_strongCompatibility_punctured_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {R t : ℝ} {z a : ℂ} (hR : 0 < R)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ {a} ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ {a}) z t) ⊆ ball 0 R \ {a}) :
    closure (Λ t) = closure (clusterOn μ (ball (0 : ℂ) R \ {a}) z t) := by
  rcases hcl with hΛcl | hcl
  · exact regularizedFamily_closure_eq_clusterOn_punctured_disc hμ hR (hV R hR)
      ha hz ht hΛ (hΛcl.trans sdiff_subset)
  · have hc := closure_clusterOn_punctured_disc_eq hμ hR (hV R hR) ha hz ht
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

#print axioms leastSupersolution_eq_zero_of_punctured_admissible
#print axioms regularizedFamily_strongCompatibility_punctured_disc
#print axioms tendsto_leastSupersolutionOn_punctured_disc_at_puncture
#print axioms continuousWithinAt_punctured_infimum_iff
#print axioms closure_sdiff_singleton_of_isOpen
#print axioms closure_clusterOn_punctured_disc_eq
#print axioms regularizedFamily_closure_eq_clusterOn_punctured_disc

end HarmonicBalls
