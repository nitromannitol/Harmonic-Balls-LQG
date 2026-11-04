import HarmonicBalls.Proofs.Sec10.UniqueComplementFrontier
import HarmonicBalls.Proofs.Sec6.VolumeGrowthAssembly

/-! # Complementary frontiers from the annulus estimates

The Section 6 annulus estimates supply the component Harnack estimate used
in the local-connectivity argument. The crossing-containment hypothesis is
kept explicit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Under I2 and Lemmas 6.6, 6.9 and 10.5, every complementary component
has locally connected complement and is the full complement of the cluster
closure. Its frontier is the frontier of the cluster closure. -/
theorem ae_complement_frontier_geometry_of_annulus_estimates
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h66 : ManyVeryGoodAnnuliStmt.{u})
    (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        IsLocallyConnectedSet Uᶜ ∧
        U = (closure (cluster (μ ω) 1 z t))ᶜ ∧
        frontier U = frontier (closure (cluster (μ ω) 1 z t)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  have h6 : HarnackTypeComponentStmt.{u} :=
    harnackTypeComponentStmt_of_lemmas h66
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure hI2 h69)
  filter_upwards [ae_complement_locallyConnected_of_crossing
      hI2 h6 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_complement_component_eq_and_frontier_of_crossing
      hI2 h5 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hlocal hfrontier
  intro t ht z hz hcl U hU
  exact ⟨hlocal t ht z hz hcl U hU, hfrontier t ht z hz hcl U hU⟩

end HarmonicBalls
