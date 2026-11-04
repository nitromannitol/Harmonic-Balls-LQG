import HarmonicBalls.Proofs.Sec5.ClusterGeometricScaling
import HarmonicBalls.Proofs.Sec5.DyadicIntervals

/-! # Dyadic local cluster estimates from normalized pullbacks -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set ProbabilityTheory Filter

/-- Unit-scale estimates for every dyadically normalized pullback give the
scaled local estimates used in the cofinal-interval construction. -/
theorem cofinalRegularizedClusterIntervals_of_normalizedDyadicEstimates
    (hnormalized : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∃ T : ℕ → Ω → ℝ, (∀ n, IdentDistrib (T n) (T 0) P P) ∧
          (∀ᵐ ω ∂P, 0 < T 0 ω) ∧
          ∀ᵐ ω ∂P, ∀ n, ∀ z ∈ ball (0 : ℂ) (1 / 2),
            SatisfiesHarmonicBallConditionsOn
              (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω))
              (regularizedCluster
                (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z) z (T n ω) ∧
            ∀ t ∈ Ioo 0 (T n ω),
              closure (cluster
                (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z t) ⊆ ball 0 1 ∧
              normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)
                (frontier (cluster
                  (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z t)) = 0) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  apply cofinalRegularizedClusterIntervals_of_dyadicEstimates
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨T, hlaw, hpos, hlocal⟩ := hnormalized γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  refine ⟨T, hlaw, hpos, ?_⟩
  filter_upwards [hlocal] with ω hω
  intro n z hz _
  have h := uniformLocalClusterProperties_normalizedPullback_scale
    (γ := γ) (α₀ := α₀) (hcirc := hcirc ω) (μ := μ ω)
    (k := (2 : ℝ) ^ n) (H := T n ω) (by positivity) (hω n)
  simpa only [dyadicClusterScaleFactor] using h z hz

end HarmonicBalls
