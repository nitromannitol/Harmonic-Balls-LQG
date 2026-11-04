import HarmonicBalls.Proofs.Sec10.CrossingsAssembly
import HarmonicBalls.Proofs.Sec10.ComplementFrontierAssembly
import HarmonicBalls.Proofs.Sec10.NullPerfectFrontier
import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator

/-! # Section 10 consequences of volume growth

The Brownian odometer comparison is supplied by volume growth. The annular
prevalence, crossing-containment and typical-scale inputs remain explicit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Lemma 10.1 from volume growth, annular prevalence, and the staged affine
invariance and coordinate-change inputs. -/
theorem clusterBoundedCrossings_of_volumeGrowth_and_prevalence
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h66 : ManyVeryGoodAnnuliStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_prevalence_and_comparison hI2
    (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2) h66 hAff hCC

/-- Lemma 10.1 from volume growth, the subrange prevalence step, and the
staged LQG existence, Weyl scaling, affine invariance and coordinate-change
inputs. -/
theorem clusterBoundedCrossings_of_volumeGrowth_and_subrange
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_volumeGrowth_and_prevalence hI2
    (manyVeryGoodAnnuliStmt_of_literature hsub hex hW) hAff hCC

/-- Volume growth, annular prevalence and crossing containment imply the
local connectivity and uniqueness of each complementary component. -/
theorem ae_complement_frontier_geometry_of_volumeGrowth_and_prevalence
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h66 : ManyVeryGoodAnnuliStmt.{u})
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
        frontier U = frontier (closure (cluster (μ ω) 1 z t)) :=
  ae_complement_frontier_geometry_of_annulus_estimates hI2 h66
    (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2) h5

/-- Volume growth and the typical-point good-scale estimate imply that all
complementary frontiers are compact, perfect and have zero Liouville mass. -/
theorem ae_cluster_complement_frontier_null_perfect_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        (frontier U).Nonempty ∧ IsCompact (frontier U) ∧ Perfect (frontier U) ∧
          μ ω (frontier U) = 0 :=
  ae_cluster_complement_frontier_null_perfect_of_harmonicMeasure hI2
    (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2) h82

end HarmonicBalls
