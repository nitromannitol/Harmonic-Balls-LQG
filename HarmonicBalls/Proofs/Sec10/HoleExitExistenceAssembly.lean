import HarmonicBalls.Proofs.Sec10.HolePointExitTime
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences
import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences

/-! # Pointwise hole exit from staged LQG inputs

The Section 2 mass estimate and Section 6 prevalence results supply the
volume-growth and Harnack assumptions in the pointwise hole-exit theorem.
The LQG inputs are staged pending source review; the Section 6 chain awaits
audit. The typical-point good-scale estimate remains explicit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

section

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureCoordChange P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureExistence P γ α hC hcirc)

include hDG hCC hE

/-- Under the three staged LQG inputs and Lemma 8.2, a point in a bounded
cluster hole remains in a hole until a finite exit time at which it lies on
the cluster frontier. No existence or absence of holes is asserted. -/
theorem ae_cluster_hole_point_exit_on_frontier_of_existence
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, ∀ x : ℂ,
      x ∈ (closure (cluster (μ ω) 1 z t))ᶜ →
      Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ x) →
      ∃ L : ℝ, t < L ∧
        (∀ s : ℝ, t ≤ s → s < L →
          x ∈ (closure (cluster (μ ω) 1 z s))ᶜ ∧
          Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z s))ᶜ x)) ∧
        x ∈ frontier (cluster (μ ω) 1 z L) ∧
        (∀ s : ℝ, L ≤ s → x ∈ closure (cluster (μ ω) 1 z s)) := by
  have hI2 := lqgVolumeGrowthAllScalesStmt_of_existence hDG hCC hE
  exact ae_cluster_hole_point_exit_on_frontier hI2
    (liouvilleVolumeGrowthStmt_of_existence hDG hCC hE)
    (Section6.harnackTypeEstimateStmt_of_volumeGrowth_zero_existence hI2
      (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc))
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82

end

end HarmonicBalls
