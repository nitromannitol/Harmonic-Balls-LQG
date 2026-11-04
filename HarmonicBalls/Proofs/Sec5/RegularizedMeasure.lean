import HarmonicBalls.Proofs.Sec5.RegularizedGeometry

/-!
# Measure of regularized clusters

For an open cluster, regularization changes only boundary points. Thus a
null boundary gives the same mass and a null boundary for the regularization,
as used in the paragraph preceding Proposition 5.4 (lines 846–851).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- An open cluster is contained in its regularization. -/
theorem cluster_subset_regularizedCluster {μ : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hopen : IsOpen (cluster μ r z t)) : cluster μ r z t ⊆ regularizedCluster μ r z t :=
  hopen.subset_interior_iff.2 subset_closure

/-- Regularization of an open cluster adds only points of its boundary. -/
theorem regularizedCluster_sdiff_subset_frontier {μ : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hopen : IsOpen (cluster μ r z t)) :
    regularizedCluster μ r z t \ cluster μ r z t ⊆ frontier (cluster μ r z t) := by
  rw [frontier, hopen.interior_eq]
  intro x hx
  exact ⟨interior_subset hx.1, hx.2⟩

/-- The boundary of a regularized open cluster is contained in the original boundary. -/
theorem frontier_regularizedCluster_subset {μ : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hopen : IsOpen (cluster μ r z t)) :
    frontier (regularizedCluster μ r z t) ⊆ frontier (cluster μ r z t) := by
  rw [frontier, (isOpen_regularizedCluster μ r z t).interior_eq, frontier, hopen.interior_eq]
  intro x hx
  refine ⟨?_, fun h => hx.2 (cluster_subset_regularizedCluster hopen h)⟩
  exact closure_minimal interior_subset isClosed_closure hx.1

/-- Regularization preserves mass when the original cluster has null boundary. -/
theorem measure_regularizedCluster_eq {μ : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hopen : IsOpen (cluster μ r z t)) (hnull : μ (frontier (cluster μ r z t)) = 0) :
    μ (regularizedCluster μ r z t) = μ (cluster μ r z t) := by
  symm
  exact measure_eq_measure_of_null_sdiff (cluster_subset_regularizedCluster hopen)
    (measure_mono_null (regularizedCluster_sdiff_subset_frontier hopen) hnull)

/-- Null boundary is preserved by regularization. -/
theorem measure_frontier_regularizedCluster_eq_zero {μ : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hopen : IsOpen (cluster μ r z t)) (hnull : μ (frontier (cluster μ r z t)) = 0) :
    μ (frontier (regularizedCluster μ r z t)) = 0 :=
  measure_mono_null (frontier_regularizedCluster_subset hopen) hnull

end HarmonicBalls
