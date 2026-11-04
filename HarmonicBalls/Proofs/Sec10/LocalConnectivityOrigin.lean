import HarmonicBalls.Proofs.Sec10.LocalConnectivityFromCrossings

/-!
# Local connectivity when the origin avoids the cluster boundary

The compact-continuum crossing theorem removes the geometric premise from the
local-connectivity reduction. The only remaining point excluded by the
localized crossing estimate is the origin.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Conditional on volume growth and Lemmas 6.2 and 10.5, every complementary
component has locally connected complement whenever the origin is not on its
boundary. -/
theorem ae_complement_locallyConnected_of_origin_not_mem_frontier_proved_crossing
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        (0 : ℂ) ∉ frontier U → IsLocallyConnectedSet Uᶜ := by
  apply ae_complement_locallyConnected_of_origin_not_mem_frontier hI2 h6 h5
  intro w r R _ hrR K hKc hK hKball hcross
  exact IsConnected.exists_annular_component_crossing hK hKc w hrR hKball hcross

/-- The same conclusion holds for every complementary component when the
origin is outside the cluster frontier. -/
theorem ae_complement_locallyConnected_of_origin_not_mem_cluster_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      (0 : ℂ) ∉ frontier (cluster (μ ω) 1 z t) →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        IsLocallyConnectedSet Uᶜ := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_complement_locallyConnected_of_origin_not_mem_frontier_proved_crossing
      hI2 h6 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2] with ω hlocal hgeom
  intro t ht z hz hcl hzero U hU
  apply hlocal t ht z hz hcl U hU
  exact fun h => hzero ((hgeom t 1 ht zero_lt_one z hz hcl U hU).2.2.2.1 h)

/-- In particular, the conclusion holds for every cluster that contains the
origin, even when its pole is elsewhere. -/
theorem ae_complement_locallyConnected_of_origin_mem_cluster
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      (0 : ℂ) ∈ cluster (μ ω) 1 z t →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        IsLocallyConnectedSet Uᶜ := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_complement_locallyConnected_of_origin_not_mem_cluster_frontier
      hI2 h6 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hlocal hopen
  intro t ht z hz hcl hzero U hU
  apply hlocal t ht z hz hcl _ U hU
  rw [(hopen t 1 ht zero_lt_one z hz).1.frontier_eq]
  exact fun h => h.2 hzero

end HarmonicBalls
