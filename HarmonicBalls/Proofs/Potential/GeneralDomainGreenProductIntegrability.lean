import HarmonicBalls.Proofs.Potential.BoundedDomainGreenMeasurability
import HarmonicBalls.Proofs.Potential.DiscFiniteSourceLaplacian
import HarmonicBalls.Proofs.Sec6.GreenIntegrability

/-!
# Integrability of the Green kernel on a bounded domain

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- The Green kernel is integrable against a finite source concentrated in a
bounded open domain and planar volume restricted to the domain. -/
theorem generalDomain_green_integrable_product_volume {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V) :
    Integrable (fun p : ℂ × ℂ => greenFunction V p.1 p.2)
      (ν.prod (volume.restrict V)) := by
  obtain ⟨r, hr⟩ := hVb.subset_ball (0 : ℂ)
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsub : V ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left _ _))
  have hνR : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R :=
    hν.mono fun _ hy => ball_subset_closedBall (hsub hy)
  have hb := (disc_green_integrable_product_volume hR hνR).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_mono hsub le_rfl))
  exact hb.mono_nonneg (measurable_greenFunction_uncurry hV).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => greenFunction_nonneg hVb p.1 p.2)
    (Filter.Eventually.of_forall fun p =>
      Section6.greenFunction_le_of_subset hsub isBounded_ball p.1 p.2)

/-- The literal transposed Green potential is integrable on the domain. -/
theorem integrableOn_generalDomain_transposedGreenPotential {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V) :
    IntegrableOn (fun x => ∫ y, greenFunction V y x ∂ν) V :=
  (generalDomain_green_integrable_product_volume hV hVb hν).integral_prod_right

/-- The literal transposed Green potential is locally integrable on the domain. -/
theorem locallyIntegrableOn_generalDomain_transposedGreenPotential {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V) :
    LocallyIntegrableOn (fun x => ∫ y, greenFunction V y x ∂ν) V :=
  (integrableOn_generalDomain_transposedGreenPotential hV hVb hν).locallyIntegrableOn


end HarmonicBalls
