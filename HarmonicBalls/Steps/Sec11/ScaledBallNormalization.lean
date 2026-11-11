import HarmonicBalls.Steps.Sec11.ScaledBallPunctureRemoval

/-! # Exponential normalization of local metric estimates

A local diameter estimate with a random exponential normalization can be
combined with a tail bound for its logarithm. Both estimates are explicit
hypotheses; this file does not assert them for the LQG metric.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory
open scoped ENNReal

/-- Split a local metric exceedance into the normalized metric exceedance and
an exceptional event for the logarithmic normalization. -/
theorem measure_internalMetric_exceedance_le_of_log_normalization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (A : Ω → ℝ≥0∞) (H : Ω → ℝ)
    (K W : Set ℂ) (κ β t : ℝ) (p q : ℝ≥0∞)
    (htail : P {ω | ∃ x ∈ K, ∃ y ∈ K,
      A ω * ENNReal.ofReal (Real.exp (-κ * t + H ω)) <
        internalMetric (D ω) W x y} ≤ p)
    (hlog : P {ω | (κ - β) * t < H ω} ≤ q) :
    P {ω | ∃ x ∈ K, ∃ y ∈ K,
      A ω * ENNReal.ofReal (Real.exp (-β * t)) <
        internalMetric (D ω) W x y} ≤ p + q := by
  calc
    _ ≤ P ({ω | ∃ x ∈ K, ∃ y ∈ K,
        A ω * ENNReal.ofReal (Real.exp (-κ * t + H ω)) <
          internalMetric (D ω) W x y} ∪ {ω | (κ - β) * t < H ω}) := by
      apply measure_mono
      intro ω ⟨x, hx, y, hy, hxy⟩
      by_cases h : (κ - β) * t < H ω
      · exact Or.inr h
      · left
        refine ⟨x, hx, y, hy, lt_of_le_of_lt ?_ hxy⟩
        gcongr
        linarith
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add htail hlog)

/-- The scaled-ball puncture criterion follows from separate summable bounds
on normalized local distances and on the logarithmic normalizations. -/
theorem exists_scaled_ball_criterion_of_log_normalization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D E : Ω → ℂ → ℂ → ℝ) (A : Ω → ℝ≥0∞) (s ξ α β κ : ℝ)
    (hξ : 0 ≤ ξ) (hα : 0 ≤ α) (hgap : ξ * α < β)
    (V : Set ℂ) (hball : ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hA : ∀ᵐ ω ∂P, A ω ≠ ∞)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ∀ (H : Ω → ℕ → ℕ → ℝ) (p q : ℕ → ℝ≥0∞),
        (∑' n, p n) ≠ ∞ → (∑' n, q n) ≠ ∞ →
        (∀ (n i : ℕ), i ≤ N →
          P {ω | ∃ x ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
            ∃ y ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
              A ω * ENNReal.ofReal (Real.exp (-κ * (n : ℝ) + H ω n i)) <
                internalMetric (D ω)
                  (ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε)))
                  x y} ≤ p n) →
        (∀ (n i : ℕ), i ≤ N → P {ω | (κ - β) * (n : ℝ) < H ω n i} ≤ q n) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_for_puncture_removal P D E A s ξ α β hξ hα hgap
      V hball hD hE hDnonneg hEnonneg hA hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro H p q hp hq htail hlog
  apply hcriterion (fun n => p n + q n)
  · rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hp, hq⟩
  · intro n i hi
    exact measure_internalMetric_exceedance_le_of_log_normalization P D A
      (fun ω => H ω n i) _ _ κ β n (p n) (q n) (htail n i hi) (hlog n i hi)


end HarmonicBalls
