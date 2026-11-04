import HarmonicBalls.Proofs.Sec10.IsolatedLocalConnectivity
import HarmonicBalls.Proofs.Sec10.CrossingImpliesNoHoles

/-!
# Local connectivity of cluster closures

The crossing-containment hypothesis forces the complement of a compactly
contained cluster closure to be connected. Thus the local connectivity of the
complement of each complementary component applies to the cluster closure.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Under volume growth and Lemmas 6.2 and 10.5, cluster closures compactly
contained in the unit disk are locally connected. -/
theorem ae_cluster_closure_locallyConnected_of_crossing
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      IsLocallyConnectedSet (closure (cluster (μ ω) 1 z t)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_complement_locallyConnected_of_crossing
      hI2 h6 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_compl_closure_connected_of_crossing_containment
      hI2 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hlocal hconnected
  intro t ht z hz hcl
  have htwo : (2 : ℂ) ∈ (closure (cluster (μ ω) 1 z t))ᶜ := by
    intro h
    have hball := hcl h
    have hdist : dist (2 : ℂ) 0 < 1 := mem_ball.mp hball
    norm_num [dist_eq_norm] at hdist
  have hU : connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ (2 : ℂ) ∈
      connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ := ⟨2, htwo, rfl⟩
  have hresult := hlocal t ht z hz hcl _ hU
  rw [(hconnected t ht z hz hcl).isPreconnected.connectedComponentIn htwo, compl_compl] at hresult
  exact hresult

end HarmonicBalls
