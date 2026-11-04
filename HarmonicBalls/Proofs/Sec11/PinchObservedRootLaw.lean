import HarmonicBalls.Proofs.Sec11.PinchUnnormalizedKernel

/-! # Rooted comparison through field observables

A rooted comparison need only hold for the observations that determine the
property of interest. The reference field need not be realized as a shift of
the original sample space. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-- Transfer a property of a measurable observation from fixed-root comparison
laws to typical points of a random measure. The rooted-law comparison takes
place after mapping the source law to the observation space. -/
theorem ae_ae_of_observed_unnormalized_rooted_law
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
    (hrooted : ∀ n,
      (P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
        (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw)).map
          (fun x => (observe x.1, x.2)) ≪ shiftedRootReferenceLaw (ρ n) R (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, R.map (fun ω => shift n (z, ω)) ≪ Q n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ f ∂Q n z, p (f, z)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p (observe ω, z) := by
  apply ae_ae_of_rooted_positive_weight P μ hμ hloc w hw hpos hfin
    (fun n => P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw))
  · intro n
    apply weightedRestrictionKernel_compProd_ac_canonical
    filter_upwards [hloc] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω
    exact weightedLocalization_measure_ne_top (μ ω) hw n
  · intro n
    have href : ∀ᵐ x ∂shiftedRootReferenceLaw (ρ n) R (shift n), p x :=
      ae_shiftedRootReferenceLaw_of_ae_comparison (ρ n) R (shift n)
        (hshift n) (Q n) hp (hac n) (hfixed n)
    have hsource := (hrooted n).ae_le href
    exact ae_of_ae_map (hobserve.comp measurable_fst |>.prodMk measurable_snd).aemeasurable hsource

#print axioms ae_ae_of_observed_unnormalized_rooted_law

end HarmonicBalls
