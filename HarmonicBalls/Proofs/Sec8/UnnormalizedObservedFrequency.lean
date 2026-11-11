import HarmonicBalls.Proofs.Sec8.RootedObservedFrequency
import HarmonicBalls.Proofs.Sec8.RootedSamplingEquivalence

/-! # Observable frequency under an unnormalized rooted law

The imported phase-frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. -/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A convergent normalized rooted approximation represents the frequency
also under the unnormalized weighted rooted law. -/
theorem exists_observed_frequency_event_unnormalizedWeightedRestriction_compProd
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞)
    (observe : Ω → F) (hobserve : Measurable observe) (ε : ℝ) (hε : 0 < ε)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V)
    (f : S → ℕ → F × ℂ → ℝ) (hf : ∀ V n, Measurable (f V n))
    (hlim : ∀ V, TendstoInMeasure (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw)
      (fun n x => f V n (observe x.1, x.2)) atTop
      (fun x => (normalizedRestriction
        ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) V.val).toReal))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b}) :
    ∃ E : Set (F × ℂ), MeasurableSet E ∧
      ∀ᵐ x ∂(P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hμ B hB w hw),
        ((observe x.1, x.2) ∈ E ↔ ∀ᶠ N : ℕ in atTop,
          (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ x.1) β x.2 N₀
            a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) := by
  obtain ⟨E, hE, hEq⟩ :=
    exists_observed_frequency_event_weightedRestriction_compProd
      P μ hμ hloc B hB w hw hmass observe hobserve ε hε S hcount hgen hpi hsets
      f hf hlim β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  refine ⟨E, hE, ?_⟩
  exact (unnormalizedWeightedRestrictionKernel_compProd_ac_normalized
    P μ hμ B hB w hw (hmass.mono fun _ h => h.2)).ae_le hEq

/-- Observable events may depend on the member of a countable cover. If each
represents the same property under the corresponding rooted law and holds
under its reference law, that property holds at almost every sampled point. -/
theorem ae_ae_of_observed_events_on_weighted_cover
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : ℕ → Set ℂ) (hB : ∀ n, MeasurableSet (B n))
    (hcover : ∀ z, ∃ n, z ∈ B n) (w : ℕ → ℂ → ℝ≥0∞)
    (hw : ∀ n, Measurable (w n))
    (hpos : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (B n), w n z ≠ 0)
    (hfin : ∀ n, ∀ᵐ ω ∂P, ((μ ω).withDensity (w n)) (B n) ≠ ∞)
    (observe : Ω × ℂ → F) (hobserve : Measurable observe)
    (R : ℕ → Measure F) (p : Ω → ℂ → Prop)
    (hrooted : ∀ n,
      (P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hμ (B n) (hB n) (w n) (hw n)).map
        observe ≪ R n)
    (hevents : ∀ n, ∃ E : Set F, MeasurableSet E ∧
      (∀ᵐ y ∂(R n), y ∈ E) ∧
      (∀ᵐ x ∂(P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hμ (B n) (hB n) (w n) (hw n)),
        observe x ∈ E ↔ p x.1 x.2)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p ω z := by
  let ν : ℕ → Measure (Ω × ℂ) := fun n =>
    P ⊗ₘ weightedRestrictionKernel P μ hμ (B n) (hB n) (w n) (hw n)
  apply ae_ae_of_rooted_weighted_cover_of_aemeasurable P μ hμ B hB hcover w hw hpos hfin ν
  · intro n
    exact Measure.AbsolutelyContinuous.rfl
  · intro n
    obtain ⟨E, hE, href, hequiv⟩ := hevents n
    have hsource := ae_of_ae_map hobserve.aemeasurable ((hrooted n).ae_le href)
    have hac := weightedRestrictionKernel_compProd_ac_canonical
      P μ hμ (B n) (hB n) (w n) (hw n) (hfin n)
    filter_upwards [hac.ae_le hsource, hac.ae_le hequiv] with x hx hx'
    exact hx'.mp hx

end HarmonicBalls
