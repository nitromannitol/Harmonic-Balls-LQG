import HarmonicBalls.Proofs.Sec10.FrontierPerfect
import HarmonicBalls.Proofs.Sec8.ClusterBoundary
import HarmonicBalls.Proofs.Sec6.VolumeGrowthAssembly

/-! # Null perfect complementary frontiers

The zero-mass cluster-boundary estimate transfers to each complementary
frontier. The perfectness result uses volume growth alone.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- For compactly contained clusters, every complementary frontier is a
nonempty compact perfect set of zero Liouville mass. -/
theorem ae_cluster_complement_frontier_null_perfect
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h81 : BoundaryMeasureZeroOfCompactClusterStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        (frontier U).Nonempty ∧ IsCompact (frontier U) ∧ Perfect (frontier U) ∧
          μ ω (frontier U) = 0 := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_frontier_perfect hI2 γ hγ hγ2 α₀ hα
      Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    h81 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hperfect hgeom hnull
  intro t ht z hz hcl U hU
  have hp := hperfect t ht z hz hcl U hU
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hcompact : IsCompact (frontier U) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_frontier
      (fun q hq => ball_subset_closedBall (hg.2.2.2.2 (subset_closure hq)))
  exact ⟨hp.1, hcompact, hp.2.1,
    measure_mono_null hg.2.2.2.1 (hnull t ht z hz hcl)⟩

/-- The null perfect frontier conclusion follows from volume growth,
the Brownian odometer comparison, and the typical-point good-scale estimate. -/
theorem ae_cluster_complement_frontier_null_perfect_of_harmonicMeasure
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h69 : OdometerHarmonicMeasureBoundStmt.{u})
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
  ae_cluster_complement_frontier_null_perfect hI2
    (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure hI2 h69) h82)

end HarmonicBalls
