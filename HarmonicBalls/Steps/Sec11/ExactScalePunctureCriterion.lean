import HarmonicBalls.Steps.Sec11.AsymptoticPunctureCriterion

/-! # Puncture removal with exact LQG scaling

For a strong LQG metric, the natural deterministic scaling constant is
`r ^ (ξ * Q)`. This file specializes the puncture criterion to that explicit
normalization. The compact-diameter moment bound and its identification with
the metric of the field remain hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

/-- The puncture-removal criterion with the exact power normalization. The
compact-diameter moment estimate is still required for each cover ball. -/
theorem exists_scaled_ball_criterion_of_exact_scale_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hh : IsWholePlaneGFF P hC hcirc)
    (D E : Ω → ℂ → ℂ → ℝ) (s γ ξ α : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ)
    (V : Set ℂ) (hball : ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hmeasD : ∀ x y, Measurable fun ω => D ω x y)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ (n : ℕ),
        (∫⁻ ω, scaledCompactInternalDiameter D hcirc ξ (closedBall (c i) ε)
          (ball (c i) (2 * ε)) (Real.exp (-(s + n)))
          (ENNReal.ofReal (Real.rpow (Real.exp (-(s + n))) (ξ * lqgQ γ))) ω ∂P) ≤ B) →
      ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
        internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y) := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_exponent_and_compact_moments P hC hcirc hh D E
      s γ ξ α hs hξ hα hαQ V hball hmeasD hD hE hDnonneg hEnonneg hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro hmom
  apply hcriterion (fun r => ENNReal.ofReal (Real.rpow r (ξ * lqgQ γ))) (fun _ => 0) 1
  · intro n
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (Real.exp_pos _) _)).ne'
  · intro n
    exact ENNReal.ofReal_ne_top
  · exact ENNReal.one_ne_top
  · exact tendsto_const_nhds
  · filter_upwards with r
    simp only [add_zero, one_mul, le_refl]
  · exact hmom


end HarmonicBalls
