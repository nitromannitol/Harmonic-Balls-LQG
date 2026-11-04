import HarmonicBalls.Proofs.Sec11.PinchObservedRootLaw
import HarmonicBalls.Steps.Sec11.PinchBlockMeasurable

/-! # Rooted transfer of block-frequency bounds

The observable can describe a field modulo constants or another measurable
encoding sufficient to determine the events. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-- A common fixed-root block-frequency bound transfers through rooted
comparison to typical points. Joint measurability is required only for each
individual scale event. -/
theorem ae_ae_block_density_of_observed_rooted_law
    {Ω Ξ F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (R : Measure Ξ) [SFinite R]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (observe : Ω → F) (hobserve : Measurable observe)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ξ → F)
    (hshift : ∀ n, Measurable (shift n)) (Q : ℕ → ℂ → Measure F)
    (E : ℕ → F × ℂ → Prop) (hE : ∀ n, MeasurableSet {x | E n x}) (q : ℝ)
    (hrooted : ∀ n,
      (P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
        (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw)).map
          (fun x => (observe x.1, x.2)) ≪ shiftedRootReferenceLaw (ρ n) R (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, R.map (fun ω => shift n (z, ω)) ≪ Q n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ f ∂Q n z, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧ E k (f, z)}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧ E k (observe ω, z)}.ncard : ℝ) :=
  ae_ae_of_observed_unnormalized_rooted_law P R μ hμ hloc w hw hpos hfin observe hobserve
    ρ shift hshift Q (measurableSet_eventually_blockEvent_ncard E hE q) hrooted hac hfixed

#print axioms ae_ae_block_density_of_observed_rooted_law

end HarmonicBalls
