import HarmonicBalls.Steps.Sec11.InternalPinchScales
import HarmonicBalls.Proofs.Sec11.PinchMetricBall

/-!
# Pinch-scale frequencies from internal-metric bounds

The frequency hypothesis below remains to be established from positive
probability, scaling, locality and the typical-point change of measure. The
metric-field axioms are staged in `HarmonicBalls.Proposed.LQG` and remain
pending source review.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Finset
open scoped ENNReal Topology BigOperators

universe u

open Classical in
/-- Lemma 11.13 follows if the strengthened pinch event has a deterministic,
positive limiting frequency at almost every LQG-typical point. -/
theorem manyPinchScalesStmt_of_internalFrequency
    (U T Q' Q : Set ℂ) (hconfig : IsPinchPointConfiguration U T Q' Q)
    (hfreq : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ M : ℝ, 0 < M → ∃ q : ℝ, 0 < q ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        IsLQGMetricOfField P γ ξ α₀ hC D →
      ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N,
          if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z
          then (1 : ℝ) else 0) / (N : ℝ)) atTop (𝓝 q))
    (hmetric : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) : ManyPinchScalesStmt.{u} := by
  refine ⟨U, T, Q', Q, hconfig, ?_⟩
  intro γ α₀ ξ hγ hγ2 hα M hM
  obtain ⟨q, hq, hfreq⟩ := hfreq γ α₀ ξ hγ hγ2 hα M hM
  let δ : ℝ := min (q / 2) (1 / 2)
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := by
    dsimp [δ]
    constructor
    · exact lt_min (by linarith) (by norm_num)
    · have := min_le_right (q / 2) (1 / 2 : ℝ)
      linarith
  have hδq : δ < q := by
    have := min_le_left (q / 2) (1 / 2 : ℝ)
    dsimp [δ]
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ P hC hcirc μ D hGFF hμ hD
  filter_upwards [hfreq Ω P hC hcirc μ D hGFF hμ hD,
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      (hmetric Ω P γ ξ α₀ hC hcirc) hGFF hγ hγ2 hα hD] with ω hfreqω hDω
  filter_upwards [hfreqω] with z hz
  exact eventually_pinchPointEvent_block_ncard_of_internalFrequency hDω hδq hz

end HarmonicBalls
