import HarmonicBalls.Proofs.Sec9.BoundaryExteriorDefect
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic

/-! # Comparison with countable common frontier

Volume growth rules out atoms. Therefore a countable intersection of the
cluster and comparison-ball frontiers is enough for the set inclusions in
weak uniqueness, without invoking the typical-scale boundary estimate.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Under I2, every subharmonic comparison ball whose frontier meets the
cluster frontier in only countably many points lies between the cluster and
its regularization. -/
theorem ae_subharmonicBall_sandwich_of_countable_common_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      (frontier (cluster (μ ω) R z t) ∩ frontier A).Countable →
      cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
      (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_subharmonicBall_uniqueness_of_null_common_frontier hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hV hcompare
  let : NullSingletonClass (μ ω) := ⟨fun x => by
    have hR : 0 < ‖x‖ + 1 := by positivity
    have hx : x ∈ ball (0 : ℂ) (‖x‖ + 1) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    exact (hV.2 (‖x‖ + 1) hR).measure_singleton hx⟩
  intro A z t R ht hR hz hcl hA hmass hcount
  exact hcompare A z t R ht hR hz hcl hA hmass (hcount.measure_zero (μ ω))

/-- If inclusion in the regularized cluster fails, the two frontiers meet in
an uncountable set of positive Liouville mass. -/
theorem ae_subharmonicBall_comparison_failure_common_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      ¬ A ⊆ regularizedCluster (μ ω) R z t →
      ¬ (frontier (cluster (μ ω) R z t) ∩ frontier A).Countable ∧
      0 < μ ω (frontier (cluster (μ ω) R z t) ∩ frontier A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_sandwich_of_countable_common_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_subharmonicBall_uniqueness_of_null_common_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcount hnull
  intro A z t R ht hR hz hcl hA hmass hfail
  constructor
  · intro hc
    exact hfail (hcount A z t R ht hR hz hcl hA hmass hc).2.1
  · apply pos_iff_ne_zero.mpr
    intro hn
    exact hfail (hnull A z t R ht hR hz hcl hA hmass hn).2.1

end HarmonicBalls
