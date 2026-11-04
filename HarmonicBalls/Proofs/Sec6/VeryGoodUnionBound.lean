import HarmonicBalls.Draft.Section6

/-! # Union bound for the three very-good annulus criteria -/

namespace HarmonicBalls.Section6

open MeasureTheory Set
open scoped ENNReal

/-- The probability of failure of a very-good annulus is bounded by the sum
of the failure probabilities of its two size criteria and its good-annulus
prevalence criterion. No measurability of the individual events is needed. -/
theorem measure_not_veryGoodAnnulus_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (β ρ : ℝ) (x : ℂ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    P {ω | ¬ IsVeryGoodAnnulus (μ ω) β ρ x N a b C₁m C₁p C₂m C₂p C₃} ≤
      P {ω | annulusBallMassSize (μ ω) β ρ x / (μ ω) (annulus x (ρ / 4) (2 * ρ)) ∉
          Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} +
      P {ω | annulusGreenPotentialSup (μ ω) x (ρ / 4) (2 * ρ) /
          (μ ω) (annulus x (ρ / 4) (2 * ρ)) ∉
          Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} +
      P {ω | ¬ VeryGoodCriterionThree (μ ω) ρ x N a b C₃} := by
  let A : Set Ω := {ω | annulusBallMassSize (μ ω) β ρ x /
    (μ ω) (annulus x (ρ / 4) (2 * ρ)) ∉ Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)}
  let B : Set Ω := {ω | annulusGreenPotentialSup (μ ω) x (ρ / 4) (2 * ρ) /
    (μ ω) (annulus x (ρ / 4) (2 * ρ)) ∉ Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)}
  let C : Set Ω := {ω | ¬ VeryGoodCriterionThree (μ ω) ρ x N a b C₃}
  have hsub : {ω | ¬ IsVeryGoodAnnulus (μ ω) β ρ x N a b C₁m C₁p C₂m C₂p C₃} ⊆
      (A ∪ B) ∪ C := by
    intro ω hω
    by_contra h
    have ha : ω ∉ A := fun ha => h (Or.inl (Or.inl ha))
    have hb : ω ∉ B := fun hb => h (Or.inl (Or.inr hb))
    have hc : ω ∉ C := fun hc => h (Or.inr hc)
    apply hω
    rw [isVeryGoodAnnulus_iff]
    exact ⟨not_not.mp ha, not_not.mp hb, not_not.mp hc⟩
  calc
    _ ≤ P ((A ∪ B) ∪ C) := measure_mono hsub
    _ ≤ P (A ∪ B) + P C := measure_union_le _ _
    _ ≤ P A + P B + P C := by gcongr; exact measure_union_le _ _

end HarmonicBalls.Section6
