import HarmonicBalls.Proofs.Sec10.IrreducibleTwoSidedConnected
import HarmonicBalls.Proofs.Sec10.LocalConnectivityAwayFromOrigin
import HarmonicBalls.Proofs.Sec10.CenteredLocalConnectivity

/-!
# Local connectivity from annular crossings

The compact-continuum crossing premise in the earlier local-connectivity
reductions follows from the two-sided crossing theorem.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- The complement of each complementary component of a centered cluster is
locally connected, conditional on volume growth and Lemmas 6.2 and 10.5. -/
theorem ae_centered_complement_locallyConnected
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      closure (cluster (μ ω) 1 0 t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 0 t))ᶜ,
        IsLocallyConnectedSet Uᶜ := by
  apply ae_centered_complement_locallyConnected_of_compact_continuum hI2 h6 h5
  intro w r R _ hrR K hKc hK hKball hcross
  exact IsConnected.exists_annular_component_crossing hK hKc w hrR hKball hcross

/-- Every complementary cluster component has locally connected complement
after removing the origin, under the same conditional inputs. -/
theorem ae_complement_sdiff_zero_locallyConnected_of_crossing
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        IsLocallyConnectedSet (Uᶜ \ {0}) := by
  apply ae_complement_sdiff_zero_locallyConnected hI2 h6 h5
  intro w r R _ hrR K hKc hK hKball hcross
  exact IsConnected.exists_annular_component_crossing hK hKc w hrR hKball hcross

end HarmonicBalls
