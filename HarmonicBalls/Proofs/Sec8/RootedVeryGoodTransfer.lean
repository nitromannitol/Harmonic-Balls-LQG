import HarmonicBalls.Proofs.Sec8.JointVeryGoodAE
import HarmonicBalls.Proofs.Sec11.PinchUnnormalizedKernel

/-! # Rooted transfer of very-good scale frequencies

A common dominating law supplies one measurable representative of the
frequency event under both the original and fixed-root comparison laws.
The rooted comparison and the fixed-root frequency remain hypotheses.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace HarmonicBalls

/-- Transfer a fixed-root frequency estimate to points typical for the random
measure. The event retains the absolute grids in its definition. -/
theorem ae_ae_veryGoodComparableScaleFrequency_of_dominated_rooted_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (S : Measure Ω) (hPdom : P ≪ S)
    (hμS : AEMeasurable μ S) (hlocS : ∀ᵐ ω ∂S, IsLocallyFiniteMeasure (μ ω))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (R : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ S)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  obtain ⟨F, hF, hFae⟩ := exists_jointlyMeasurable_veryGoodComparableScaleFrequency
    S hμS hlocS β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  have hfixedF : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z), (ω, z) ∈ F := by
    intro n
    filter_upwards [hdom n, hfixed n] with z hdomz hfixedz
    filter_upwards [hdomz.ae_le hFae, hfixedz] with ω hω hz
    exact (hω z).2 hz
  have htarget : ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, (ω, z) ∈ F :=
    ae_ae_of_unnormalized_shiftedRootReferenceLaw P μ hμ hloc w hw hpos hfin
      ρ shift hshift R hF hrooted hac hfixedF
  filter_upwards [hPdom.ae_le hFae, htarget] with ω hω hz
  filter_upwards [hz] with z hz
  exact (hω z).1 hz

#print axioms ae_ae_veryGoodComparableScaleFrequency_of_dominated_rooted_law

end HarmonicBalls
