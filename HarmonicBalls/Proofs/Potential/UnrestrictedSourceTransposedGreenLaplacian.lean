import HarmonicBalls.Proofs.Potential.GeneralDomainTransposedFiniteSourceLaplacian

/-!
# Transposed Green potentials with unrestricted finite sources

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Set Laplacian

/-- Restricting the source to the domain preserves the literal potential, even
at observers where the Bochner integral is totalized. -/
theorem transposedGreen_integral_restrict_source {V : Set ℂ} (x : ℂ)
    (ν : Measure ℂ) :
    (∫ y, greenFunction V y x ∂(ν.restrict V)) = ∫ y, greenFunction V y x ∂ν :=
  setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun _y hy => greenFunction_of_notMem_left hy x)

/-- Both source slices are integrable at almost every observer in the domain. -/
theorem ae_transposedGreen_integrable_unrestricted_source {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] :
    ∀ᵐ x ∂(volume.restrict V),
      Integrable (fun y => greenFunction V y x) ν ∧
      Integrable (fun y => greenFunction V y x) (ν.restrict V) := by
  have hν : ∀ᵐ y ∂(ν.restrict V), y ∈ V := ae_restrict_mem hV.measurableSet
  have hp := generalDomain_green_integrable_product_volume hV hVb hν
  filter_upwards [hp.prod_left_ae] with x hx
  have hx' : IntegrableOn (fun y => greenFunction V y x) V ν := hx
  exact ⟨hx'.integrable_of_forall_notMem_eq_zero
    (fun _y hy => greenFunction_of_notMem_left hy x), hx⟩

/-- The unrestricted finite-source transposed potential is integrable on the domain. -/
theorem integrableOn_transposedGreen_unrestricted_source {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] :
    IntegrableOn (fun x => ∫ y, greenFunction V y x ∂ν) V := by
  have hν : ∀ᵐ y ∂(ν.restrict V), y ∈ V := ae_restrict_mem hV.measurableSet
  have h := integrableOn_generalDomain_transposedGreenPotential hV hVb hν
  simpa only [transposedGreen_integral_restrict_source] using h

/-- Only the source mass inside the domain contributes to the distributional
Laplacian of the literal transposed potential. -/
theorem hasLaplacian_transposedGreen_unrestricted_source {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] :
    HasLaplacian (fun x => ∫ y, greenFunction V y x ∂ν) 0 (ν.restrict V) V := by
  have hν : ∀ᵐ y ∂(ν.restrict V), y ∈ V := ae_restrict_mem hV.measurableSet
  have h := hasLaplacian_generalDomain_transposedGreenPotential hV hVb hν
  simpa only [transposedGreen_integral_restrict_source] using h


end HarmonicBalls
