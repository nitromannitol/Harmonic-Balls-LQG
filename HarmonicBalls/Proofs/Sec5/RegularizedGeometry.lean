import HarmonicBalls.Draft.Section5

/-!
# Geometry of regularized clusters

The geometric parts of Proposition 5.4 that follow directly from
`Λ̂ = interior (closure Λ)`: regular openness, connectedness and boundedness.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Every regularized cluster is regular open. -/
theorem isRegularOpen_regularizedCluster (μ : Measure ℂ) (r : ℝ) (z : ℂ) (t : ℝ) :
    IsRegularOpen (regularizedCluster μ r z t) := by
  unfold IsRegularOpen regularizedCluster
  apply Subset.antisymm
  · simpa only [closure_closure] using
      (interior_mono (closure_mono (interior_subset : interior (closure (cluster μ r z t)) ⊆
        closure (cluster μ r z t))))
  · exact isOpen_interior.subset_interior_iff.2 subset_closure

/-- A connected open cluster has a connected regularization. -/
theorem isConnected_regularizedCluster {μ : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hopen : IsOpen (cluster μ r z t)) (hconn : IsConnected (cluster μ r z t)) :
    IsConnected (regularizedCluster μ r z t) := by
  apply hconn.subset_closure
  · exact hopen.subset_interior_iff.2 subset_closure
  · exact interior_subset

/-- A bounded cluster has a bounded regularization. -/
theorem isBounded_regularizedCluster {μ : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hbound : Bornology.IsBounded (cluster μ r z t)) :
    Bornology.IsBounded (regularizedCluster μ r z t) :=
  hbound.closure.subset interior_subset

/-- Regularization preserves inclusion of clusters. -/
theorem regularizedCluster_subset_of_cluster_subset {μ : Measure ℂ} {r t₁ t₂ : ℝ} {z : ℂ}
    (h : cluster μ r z t₁ ⊆ cluster μ r z t₂) :
    regularizedCluster μ r z t₁ ⊆ regularizedCluster μ r z t₂ :=
  interior_mono (closure_mono h)

end HarmonicBalls
