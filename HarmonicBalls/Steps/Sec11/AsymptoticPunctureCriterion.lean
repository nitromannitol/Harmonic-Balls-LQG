import HarmonicBalls.Steps.Sec11.ScaleExponentAsymptotic

/-! # Puncture removal with an asymptotic scaling exponent

The exponent margin and discrete-scale conversion are consequences of
subcriticality and the stated small-radius scaling hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

/-- A scaling exponent asymptotic and compact-diameter moments imply puncture
removal, including for the endpoint α = γ. -/
theorem exists_scaled_ball_criterion_of_exponent_and_compact_moments
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
      ∀ (a : ℝ → ℝ≥0∞) (e : ℝ → ℝ) (C : ℝ≥0∞),
        (∀ n : ℕ, a (Real.exp (-(s + n))) ≠ 0) →
        (∀ n : ℕ, a (Real.exp (-(s + n))) ≠ ∞) → C ≠ ∞ →
        Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0) →
        (∀ᶠ r in 𝓝[>] (0 : ℝ),
          a r ≤ C * ENNReal.ofReal (Real.rpow r (ξ * lqgQ γ + e r))) →
        (∀ i, i ≤ N → ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ (n : ℕ),
          (∫⁻ ω, scaledCompactInternalDiameter D hcirc ξ (closedBall (c i) ε)
            (ball (c i) (2 * ε)) (Real.exp (-(s + n)))
            (a (Real.exp (-(s + n)))) ω ∂P) ≤ B) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  have hgap : ξ * α < ξ * lqgQ γ := mul_lt_mul_of_pos_left hαQ hξ
  obtain ⟨κ, hκ₁, hκ₂⟩ := exists_between hgap
  obtain ⟨β, hβ, hκ⟩ := exists_between hκ₁
  obtain ⟨η, hη, hη₂⟩ := exists_between hκ₂
  obtain ⟨θ, hθ, hθQ⟩ := exists_between hη₂
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_power_and_compact_moments P hC hcirc hh D E
      s ξ α β κ η θ hs hξ hα hβ hκ hη hθ V hball hmeasD hD hE hDnonneg hEnonneg
      hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro a e C ha0 hafin hCfin he ha hmom
  apply hcriterion (fun n => a (Real.exp (-(s + n)))) C ha0 hafin hCfin
  · exact eventually_exponential_scale_bound_of_exponent_error a s (ξ * lqgQ γ) θ e C
      hθQ he ha
  · exact hmom

#print axioms exists_scaled_ball_criterion_of_exponent_and_compact_moments

end HarmonicBalls
