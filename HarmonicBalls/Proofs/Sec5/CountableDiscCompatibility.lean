import HarmonicBalls.Proofs.Sec5.CountableDiscInadmissibility
import HarmonicBalls.Proofs.Sec5.RestrictedContainmentTest

/-! # Compatibility after countable deletions from a disc

Relatively closed countable sets may accumulate in the disc. The deleted-domain
least supersolution need not be admissible; nevertheless its cluster has the
same closure as the disc cluster.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- Removing a relatively closed countable set removes precisely its points
from the cluster. -/
theorem clusterOn_relative_countable_disc_eq_sdiff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    clusterOn μ (ball (0 : ℂ) R \ K) z t = cluster μ R z t \ K := by
  have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hz.1 ht).2.2
  have heq : leastSupersolutionOn μ (ball (0 : ℂ) R) z t = leastSupersolution μ R z t := by
    funext x
    simp only [leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hR.ne']
  have hv' : leastSupersolutionOn μ (ball (0 : ℂ) R) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R) z t := by
    rw [heq, supersolutionsOn_ball μ hR.ne']
    exact hv
  have hcontain : closure (ball (0 : ℂ) R) ⊆ ball (0 : ℂ) (R + 1) :=
    (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
      (closedBall_subset_ball (by linarith))
  have hc := clusterOn_sdiff_of_relative_countable hμ isOpen_ball isBounded_ball hcontain
    hD hK ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall)
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV) ht.le hz hv'
  simpa only [clusterOn_ball μ hR.ne'] using hc

/-- The disc and deleted-domain clusters have the same closure. -/
theorem closure_clusterOn_relative_countable_disc_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) = closure (cluster μ R z t) := by
  rw [clusterOn_relative_countable_disc_eq_sdiff hμ hR hV K hD hK hz ht]
  have hopen : IsOpen (cluster μ R z t) := by
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz.1 t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hμ hR hV hz.1 ht
  have hc : (K ∩ cluster μ R z t).Countable := hK.mono (by
    intro x hx
    exact ⟨hx.1, cluster_subset_ball hx.2⟩)
  exact closure_sdiff_countable_inter hopen hc

/-- Both compact-containment alternatives imply strong compatibility after a
relatively closed countable deletion from a disc. -/
theorem regularizedFamily_strongCompatibility_relative_countable_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ K ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆ ball 0 R \ K) :
    closure (Λ t) = closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) := by
  have hc := closure_clusterOn_relative_countable_disc_eq hμ hR (hV R hR) K hD hK hz ht
  have hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t) := by
    intro r hr hzr
    rw [(obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr (hV r hr) z hzr t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hμ hr (hV r hr) hzr ht
  rcases hcl with hΛcl | hcl
  · have heq := hΛ.2.2 t ht R hR (hΛcl.trans sdiff_subset) R le_rfl
    rw [heq, closure_regularizedCluster_eq_of_isOpen (hopen R hR hz.1), hc]
  · have hdisc : closure (cluster μ R z t) ⊆ ball (0 : ℂ) R := by
      rw [← hc]
      exact hcl.trans sdiff_subset
    have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ hR (hV R hR) hz.1 ht).2.2
    rw [hc]
    exact regularizedFamily_closure_eq_discCluster_of_compact_containment
      hR hz.1 ht hΛ hopen hv hdisc

/-- Compact containment in the deleted disc is equivalent for the
regularized family and the deleted-domain cluster. -/
theorem regularizedFamily_containment_iff_relative_countable_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z) :
    closure (Λ t) ⊆ ball (0 : ℂ) R \ K ↔
      closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆ ball 0 R \ K := by
  constructor
  · intro hcl
    rw [← regularizedFamily_strongCompatibility_relative_countable_disc
      hμ hV hR K hD hK hz ht hΛ (Or.inl hcl)]
    exact hcl
  · intro hcl
    rw [regularizedFamily_strongCompatibility_relative_countable_disc
      hμ hV hR K hD hK hz ht hΛ (Or.inr hcl)]
    exact hcl


end HarmonicBalls
