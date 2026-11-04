import HarmonicBalls.Proofs.Sec8.JointVeryGoodMeasurable

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- A random locally finite measure has a jointly measurable representative
of the eventual very-good comparable-scale event, simultaneously in the centre. -/
theorem exists_jointlyMeasurable_veryGoodComparableScaleFrequency
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {μ : Ω → Measure ℂ}
    (hμ : AEMeasurable μ P) (hfinite : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    ∃ F : Set (Ω × ℂ), MeasurableSet F ∧ ∀ᵐ ω ∂P, ∀ z : ℂ,
      (ω, z) ∈ F ↔ ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        (veryGoodComparableScaleCount (μ ω) β z N₀
          a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  obtain ⟨ν, hν, hνfinite, heq⟩ := Section6.exists_measurable_locallyFinite_rep hμ hfinite
  let F : Set (Ω × ℂ) := {p | ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
    (veryGoodComparableScaleCount (ν p.1) β p.2 N₀
      a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)}
  refine ⟨F, ?_, ?_⟩
  · exact measurableSet_eventually_veryGoodComparableScaleCount_joint
      (hν.comp measurable_fst) (fun p : Ω × ℂ => hνfinite p.1) measurable_snd β N₀
      a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  · filter_upwards [heq] with ω hω z
    simp only [F, mem_ofPred_eq, hω]

end HarmonicBalls
