import HarmonicBalls.Proofs.Sec8.GoodEventMeasurablePositive
import HarmonicBalls.Proofs.Sec8.AENormalizedRestriction

/-! # Local good-scale indicators at positive mass thresholds -/

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

open Classical MarkovProcess in
/-- Almost-sure germ-measurable normalized restrictions give local versions
of the good-scale indicators. The Brownian avoidance assumption is needed only
for the unit annulus, and no atomlessness assumption on the measures is used. -/
theorem ae_local_veryGoodComparable_indicators_of_positive_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ) (β : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ha : 0 < a)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus (0 : ℂ) 3 5, x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < μ ω V)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hrep : ∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 ε)) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  apply ae_local_veryGoodComparable_indicators_of_unit_good P germ μ β N₀
    a b C₁m C₁p C₂m C₂p C₃ m
  · apply measurableSet_isGoodAnnulus_of_ae_point_avoidance 1 (by norm_num) 0 a b ha
    simpa using hpolar
  · intro ε hε
    obtain ⟨ν, hν, heq⟩ := hrep ε hε
    refine ⟨ν, hν, ?_⟩
    filter_upwards [heq, ae_referenceBall_pos_finite P μ hfull hloc] with ω hω hpos
    refine ⟨μ ω (ball 0 ε), (hpos ε hε).1, (hpos ε hε).2, ?_⟩
    rw [hω]
    exact restrict_eq_smul_normalizedRestriction (μ ω) isOpen_ball.measurableSet
      (hpos ε hε).1 (hpos ε hε).2

end HarmonicBalls
