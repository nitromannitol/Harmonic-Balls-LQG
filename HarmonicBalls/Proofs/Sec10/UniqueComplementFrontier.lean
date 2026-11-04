import HarmonicBalls.Proofs.Sec10.ClusterClosureLocalConnectivity

/-!
# The complementary frontier under crossing containment

The frozen crossing-containment hypothesis forces each complementary
component to be the entire complement of the cluster closure. Consequently
its frontier is the frontier of that closure; no regular-open claim about
the cluster itself is used.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Under volume growth and Lemma 10.5, each complementary component is the
whole complement and its frontier is the frontier of the cluster closure. -/
theorem ae_complement_component_eq_and_frontier_of_crossing
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        U = (closure (cluster (μ ω) 1 z t))ᶜ ∧
        frontier U = frontier (closure (cluster (μ ω) 1 z t)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_compl_closure_connected_of_crossing_containment
      hI2 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hconn
  intro t ht z hz hcl U hU
  obtain ⟨p, hp, rfl⟩ := hU
  have heq := (hconn t ht z hz hcl).isPreconnected.connectedComponentIn hp
  refine ⟨heq, ?_⟩
  rw [heq, frontier_compl]

end HarmonicBalls
