import HarmonicBalls.Steps.Sec11.ScalePowerBounds

/-! # Puncture removal from scaling and compact-diameter bounds

An eventual power estimate for deterministic metric scales and compact-set
first moments supply the scale hypotheses of the puncture criterion.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Eventual power bounds and fixed-compact diameter moments imply the
logarithmic Weyl puncture-removal conclusion. -/
theorem exists_scaled_ball_criterion_of_power_and_compact_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hh : IsWholePlaneGFF P hC hcirc)
    (D E : Ω → ℂ → ℂ → ℝ) (s ξ α β κ η θ : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α)
    (hgap : ξ * α < β) (hκ : β < κ) (hη : κ < η) (hθ : η < θ)
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
      ∀ (a : ℕ → ℝ≥0∞) (C : ℝ≥0∞),
        (∀ n, a n ≠ 0) → (∀ n, a n ≠ ∞) → C ≠ ∞ →
        (∀ᶠ n in atTop, a n ≤
          C * ENNReal.ofReal (Real.exp (-θ * (s + (n : ℝ))))) →
        (∀ i, i ≤ N → ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ (n : ℕ),
          (∫⁻ ω, scaledCompactInternalDiameter D hcirc ξ (closedBall (c i) ε)
            (ball (c i) (2 * ε)) (Real.exp (-(s + n))) (a n) ω ∂P) ≤ B) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_compact_diameter_moments P hC hcirc hh D E s ξ α β κ η
      hs hξ hα hgap hκ hη V hball hmeasD hD hE hDnonneg hEnonneg hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro a C ha0 hafin hCfin hpower hmom
  obtain ⟨A, hAfin, hratio⟩ :=
    exists_uniform_scale_ratio_of_eventually_power_bound a s η θ hθ hafin C hCfin hpower
  exact hcriterion a A ha0 hafin hAfin hratio hmom


end HarmonicBalls
