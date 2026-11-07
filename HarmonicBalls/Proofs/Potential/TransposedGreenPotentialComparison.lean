import HarmonicBalls.Proofs.Potential.GeneralDomainGreenProductIntegrability

/-!
# Comparison of transposed Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter

/-- Comparison for literal source-observer Green kernels, including source integrability
and integrability of all four potentials on the ambient domain. -/
theorem transposedGreen_potential_comparison {V W : Set ℂ}
    (hV : IsOpen V) (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    (hVW : V ⊆ W) {ν ρ : Measure ℂ} [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (hνρ : ν ≤ ρ) (hν : ∀ᵐ y ∂ν, y ∈ V) (hρ : ∀ᵐ y ∂ρ, y ∈ V) :
    (∀ U ∈ ({V, W} : Set (Set ℂ)), ∀ μ ∈ ({ν, ρ} : Set (Measure ℂ)),
      IntegrableOn (fun x => ∫ y, greenFunction U y x ∂μ) W) ∧
    (∀ᵐ x ∂(volume.restrict W),
      Integrable (fun y => greenFunction V y x) ν ∧
      Integrable (fun y => greenFunction W y x) ν ∧
      Integrable (fun y => greenFunction V y x) ρ ∧
      Integrable (fun y => greenFunction W y x) ρ ∧
      0 ≤ (∫ y, greenFunction V y x ∂ν) ∧
      (∫ y, greenFunction V y x ∂ν) ≤ ∫ y, greenFunction W y x ∂ρ) := by
  have hVb := hWb.subset hVW
  have hpWρ := generalDomain_green_integrable_product_volume hW hWb
    (hρ.mono fun _ hy => hVW hy)
  have hpWν := generalDomain_green_integrable_product_volume hW hWb
    (hν.mono fun _ hy => hVW hy)
  have hpVρ : Integrable (fun p : ℂ × ℂ => greenFunction V p.1 p.2)
      (ρ.prod (volume.restrict W)) := by
    exact hpWρ.mono_nonneg (measurable_greenFunction_uncurry hV).aestronglyMeasurable
      (Eventually.of_forall fun p => greenFunction_nonneg hVb p.1 p.2)
      (Eventually.of_forall fun p => Section6.greenFunction_le_of_subset hVW hWb p.1 p.2)
  have hpVν : Integrable (fun p : ℂ × ℂ => greenFunction V p.1 p.2)
      (ν.prod (volume.restrict W)) :=
    hpVρ.mono_measure (Measure.prod_mono hνρ le_rfl)
  constructor
  · intro U hU μ hμ
    simp only [mem_insert_iff, mem_singleton_iff] at hU hμ
    rcases hU with rfl | rfl <;> rcases hμ with rfl | rfl
    · exact hpVν.integral_prod_right
    · exact hpVρ.integral_prod_right
    · exact hpWν.integral_prod_right
    · exact hpWρ.integral_prod_right
  · filter_upwards [hpVν.prod_left_ae, hpWν.prod_left_ae,
      hpVρ.prod_left_ae, hpWρ.prod_left_ae] with x h1 h2 h3 h4
    refine ⟨h1, h2, h3, h4, integral_nonneg (fun y => greenFunction_nonneg hVb y x), ?_⟩
    calc
      (∫ y, greenFunction V y x ∂ν) ≤ ∫ y, greenFunction W y x ∂ν :=
        integral_mono_ae h1 h2 (Eventually.of_forall fun y =>
          Section6.greenFunction_le_of_subset hVW hWb y x)
      _ ≤ ∫ y, greenFunction W y x ∂ρ :=
        integral_mono_measure hνρ (Eventually.of_forall fun y => greenFunction_nonneg hWb y x) h4

/-- Monotonicity in the source measure. -/
theorem transposedGreen_potential_mono_source {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν ρ : Measure ℂ} [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (hνρ : ν ≤ ρ) (hν : ∀ᵐ y ∂ν, y ∈ V) (hρ : ∀ᵐ y ∂ρ, y ∈ V) :
    ∀ᵐ x ∂(volume.restrict V),
      Integrable (fun y => greenFunction V y x) ν ∧
      Integrable (fun y => greenFunction V y x) ρ ∧
      0 ≤ (∫ y, greenFunction V y x ∂ν) ∧
      (∫ y, greenFunction V y x ∂ν) ≤ ∫ y, greenFunction V y x ∂ρ := by
  filter_upwards [(transposedGreen_potential_comparison hV hV hVb (Subset.rfl)
    hνρ hν hρ).2] with x hx
  exact ⟨hx.1, hx.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2⟩

/-- Monotonicity in the domain. -/
theorem transposedGreen_potential_mono_domain {V W : Set ℂ}
    (hV : IsOpen V) (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    (hVW : V ⊆ W) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ y ∂ν, y ∈ V) :
    ∀ᵐ x ∂(volume.restrict W),
      Integrable (fun y => greenFunction V y x) ν ∧
      Integrable (fun y => greenFunction W y x) ν ∧
      0 ≤ (∫ y, greenFunction V y x ∂ν) ∧
      (∫ y, greenFunction V y x ∂ν) ≤ ∫ y, greenFunction W y x ∂ν := by
  filter_upwards [(transposedGreen_potential_comparison hV hW hWb hVW
    (le_rfl : ν ≤ ν) hν hν).2] with x hx
  exact ⟨hx.1, hx.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2⟩

#print axioms transposedGreen_potential_comparison
#print axioms transposedGreen_potential_mono_source
#print axioms transposedGreen_potential_mono_domain

end HarmonicBalls
