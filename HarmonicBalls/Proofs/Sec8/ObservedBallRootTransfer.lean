import HarmonicBalls.Proofs.Sec8.RootedWeightDomination
import HarmonicBalls.Proofs.Sec8.JointVeryGoodMeasurable
import HarmonicBalls.Proofs.Sec11.PinchObservedRootLaw
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureScaling
import HarmonicBalls.Proofs.Sec8.AnnulusComparisonStationarity

/-! # Observable rooted transfer from ball restrictions

The rooted law can be compared after applying a measurable observation. A
measurable decoder then transfers very-good-scale estimates to the original
random measure.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- An unweighted rooted comparison on balls suffices for transfer of
properties of an observable. -/
theorem ae_ae_of_observed_unweighted_ball_rooted_law
    {Ω Ξ F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (R : Measure Ξ) [SFinite R]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (observe : Ω → F) (hobserve : Measurable observe)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ξ → F)
    (hshift : ∀ n, Measurable (shift n)) (Q : ℕ → ℂ → Measure F)
    {p : F × ℂ → Prop} (hp : MeasurableSet {x | p x})
    (hrooted : ∀ n : ℕ,
      (P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
        (ball 0 ((n : ℝ) + 1)) measurableSet_ball (fun _ => 1) measurable_const)).map
          (fun x => (observe x.1, x.2)) ≪ shiftedRootReferenceLaw (ρ n) R (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, R.map (fun ω => shift n (z, ω)) ≪ Q n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ f ∂Q n z, p (f, z)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p (observe ω, z) := by
  apply ae_ae_of_observed_unnormalized_rooted_law P R μ hμ hloc w hw hpos hfin
    observe hobserve ρ shift hshift Q hp ?_ hac hfixed
  intro n
  exact ((unnormalizedWeightedLocalization_compProd_ac_ball P μ hμ hloc w hw n).map
    (hobserve.comp measurable_fst |>.prodMk measurable_snd)).trans (hrooted n)

/-- Multiplying a measure by a finite nonzero factor leaves each
very-good comparable-scale count unchanged. -/
theorem veryGoodComparableScaleCount_smul (μ : Measure ℂ) (β : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (K : ℕ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞) :
    veryGoodComparableScaleCount (c • μ) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K =
      veryGoodComparableScaleCount μ β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K := by
  unfold veryGoodComparableScaleCount
  congr 1
  ext n
  simp only [mem_ofPred_eq, isVeryGoodAnnulus_smul μ β (dyadicScale n) z N₀
    a b C₁m C₁p C₂m C₂p C₃ hc hct, annulusBallComparison_smul μ n z m hc hct]

/-- Very-good-scale frequencies transfer through an observable rooted law
when the random measure is a finite nonzero multiple of a measurable
locally finite decoder. -/
theorem ae_ae_veryGoodComparableScaleFrequency_of_observed_ball_rooted_law
    {Ω Ξ F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (R : Measure Ξ) [SFinite R]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (observe : Ω → F) (hobserve : Measurable observe)
    (decode : F → Measure ℂ) (hdecode : Measurable decode)
    (hdecodefinite : ∀ f, IsLocallyFiniteMeasure (decode f))
    (hdecodeeq : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ ω = c • decode (observe ω))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ξ → F)
    (hshift : ∀ n, Measurable (shift n)) (Q : ℕ → ℂ → Measure F)
    (hrooted : ∀ n : ℕ,
      (P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
        (ball 0 ((n : ℝ) + 1)) measurableSet_ball (fun _ => 1) measurable_const)).map
          (fun x => (observe x.1, x.2)) ≪ shiftedRootReferenceLaw (ρ n) R (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, R.map (fun ω => shift n (z, ω)) ≪ Q n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ f ∂Q n z, ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (decode f) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m K : ℝ) := by
  let p : F × ℂ → Prop := fun x => ∀ᶠ K : ℕ in atTop,
    (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (decode x.1) β x.2 N₀
      a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)
  have hp : MeasurableSet {x | p x} :=
    measurableSet_eventually_veryGoodComparableScaleCount_joint
      (hdecode.comp measurable_fst) (fun x : F × ℂ => hdecodefinite x.1) measurable_snd
      β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  have ht := ae_ae_of_observed_unweighted_ball_rooted_law P R μ hμ hloc w hw hpos hfin
    observe hobserve ρ shift hshift Q hp hrooted hac hfixed
  filter_upwards [ht, hdecodeeq] with ω hω ⟨c, hc, hct, heq⟩
  filter_upwards [hω] with z hz
  simpa only [p, heq, veryGoodComparableScaleCount_smul _ β z N₀
    a b C₁m C₁p C₂m C₂p C₃ m _ hc hct] using hz

#print axioms veryGoodComparableScaleCount_smul
#print axioms ae_ae_of_observed_unweighted_ball_rooted_law
#print axioms ae_ae_veryGoodComparableScaleFrequency_of_observed_ball_rooted_law

end HarmonicBalls
