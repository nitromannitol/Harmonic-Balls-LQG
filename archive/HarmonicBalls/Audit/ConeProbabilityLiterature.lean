import HarmonicBalls.Steps.Sec11.ConeProbabilityFromLiterature

/-! # Conditional consumer for Lemma 11.8

This is a provider handoff, not a source admission. The proof uses Leonardo
Bonanno's Lattice-Probability formalization, including its Cameron-Martin port,
through the local smooth-shift and fixed-shift decoder developments.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

example
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ Q : Set ℂ, IsCone Q →
    ∀ M : ℝ, 0 < M → ∃ p ∈ Ioo (0 : ℝ) 1,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ z : ℂ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ)⁻¹ ^ n / 100 < infDist (0 : ℂ)
        (annulus z ((2 : ℝ)⁻¹ ^ n) (6 * (2 : ℝ)⁻¹ ^ n)) →
      ∃ A ⊆ {ω | coneMassEvent (μ ω) Q M ((2 : ℝ)⁻¹ ^ n) z},
        MeasurableSet A ∧ ENNReal.ofReal p ≤ P A := by
  exact coneBadEventProbability_of_literature hDG hCC hE

example (hS : WholePlaneScaledBallMassStep.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc) : ConeBadEventProbabilityStmt.{u} :=
  coneBadEventProbability_of_existence hS hgrowth hE

end HarmonicBalls
