import HarmonicBalls.Proofs.Sec10.UniqueComplementFrontier
import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence

/-! # Local connectivity from volume growth and LQG existence

The Section 6 prevalence argument supplies the component Harnack estimate.
Zero-strength LQG existence is a staged input pending source review; the
Section 6 dependency chain also awaits audit. Crossing containment remains
an explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Under volume growth, zero-strength LQG existence, and crossing
containment, compactly contained cluster closures are locally connected.
Every complementary component has a locally connected complement, equals
the full complement, and has the same frontier as the cluster closure. -/
theorem ae_cluster_localConnectivity_and_frontier_of_zero_existence
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      IsLocallyConnectedSet (closure (cluster (μ ω) 1 z t)) ∧
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        IsLocallyConnectedSet Uᶜ ∧
        U = (closure (cluster (μ ω) 1 z t))ᶜ ∧
        frontier U = frontier (closure (cluster (μ ω) 1 z t)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  have h6 : HarnackTypeComponentStmt.{u} :=
    Section6.harnackTypeComponentStmt_of_volumeGrowth_zero_existence hI2 hE0
  filter_upwards [ae_cluster_closure_locallyConnected_of_crossing
      hI2 h6 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_complement_locallyConnected_of_crossing
      hI2 h6 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_complement_component_eq_and_frontier_of_crossing
      hI2 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hcluster hlocal hfrontier
  intro t ht z hz hcl
  refine ⟨hcluster t ht z hz hcl, ?_⟩
  intro U hU
  exact ⟨hlocal t ht z hz hcl U hU, hfrontier t ht z hz hcl U hU⟩

end HarmonicBalls
