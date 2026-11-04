import HarmonicBalls.Proofs.Sec8.RootedKernelMeasurability

/-! # Binding and composition-product conventions for rooted fields

The unnormalized observed-root law can be expressed either by binding the
observed restricted measure or by mapping the composition product with its
kernel. This is a measure-theoretic identity and assumes no rooted-field
change-of-measure theorem. The imported Section 6 development uses Leonardo
Bonanno's whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- Binding the observed root kernel equals observing a composition product
with any s-finite kernel that represents the root measure almost surely. -/
theorem observed_bind_eq_compProd_map
    {Ω Z F : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (ν : Ω → Measure Z)
    (κ : Kernel Ω Z) [IsSFiniteKernel κ] (hκ : ∀ᵐ ω ∂P, κ ω = ν ω)
    (X : Ω → F) (hX : Measurable X) :
    (P.bind fun ω => (ν ω).map (fun z => (X ω, z))) =
      (P ⊗ₘ κ).map (fun p => (X p.1, p.2)) := by
  let K := (Kernel.deterministic X hX) ×ₖ κ
  have hm : AEMeasurable (fun ω => (ν ω).map (fun z => (X ω, z))) P := by
    apply K.aemeasurable.congr
    filter_upwards [hκ] with ω hω
    apply Measure.ext
    intro s hs
    rw [Kernel.deterministic_prod_apply' hX κ ω hs, Measure.map_apply measurable_prodMk_left hs]
    rw [hω]
  have hmap : Measurable (fun p : Ω × Z => (X p.1, p.2)) :=
    (hX.comp measurable_fst).prodMk measurable_snd
  apply Measure.ext
  intro s hs
  rw [Measure.bind_apply hs hm, Measure.map_apply hmap hs,
    Measure.compProd_apply (hmap hs)]
  apply lintegral_congr_ae
  filter_upwards [hκ] with ω hω
  rw [Measure.map_apply measurable_prodMk_left hs, hω]
  rfl

/-- For finite restricted mass, the candidate unnormalized rooted-law bind
is exactly the observed composition product of the canonical root kernel. -/
theorem observed_restricted_bind_eq_compProd_map
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (X : Ω → F) (hX : Measurable X) (B : Set ℂ) (hB : MeasurableSet B)
    (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞) :
    (P.bind fun ω => ((μ ω).restrict B).map (fun z => (X ω, z))) =
      (P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hμ B hB
        (fun _ => 1) measurable_const).map (fun p => (X p.1, p.2)) := by
  have hfin' : ∀ᵐ ω ∂P, ((μ ω).withDensity (fun _ => 1)) B ≠ ∞ := by
    simpa only [withDensity_const, one_smul] using hfin
  apply observed_bind_eq_compProd_map P (fun ω => (μ ω).restrict B)
    (unnormalizedWeightedRestrictionKernel P μ hμ B hB (fun _ => 1) measurable_const) _ X hX
  simpa only [withDensity_const, one_smul] using
    ae_unnormalizedWeightedRestrictionKernel_eq P μ hμ B hB
      (fun _ => 1) measurable_const hfin'

/-- The observed normalized root law is dominated by the unnormalized bind
law. This remains valid when the restricted mass is zero. -/
theorem observed_normalized_compProd_ac_restricted_bind
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (X : Ω → F) (hX : Measurable X) (B : Set ℂ) (hB : MeasurableSet B)
    (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞) :
    (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB (fun _ => 1) measurable_const).map
      (fun p => (X p.1, p.2)) ≪
      (P.bind fun ω => ((μ ω).restrict B).map (fun z => (X ω, z))) := by
  rw [observed_restricted_bind_eq_compProd_map P μ hμ X hX B hB hfin]
  have hfin' : ∀ᵐ ω ∂P, ((μ ω).withDensity (fun _ => 1)) B ≠ ∞ := by
    simpa only [withDensity_const, one_smul] using hfin
  exact (weightedRestrictionKernel_compProd_ac_canonical P μ hμ B hB
    (fun _ => 1) measurable_const hfin').map
      ((hX.comp measurable_fst).prodMk measurable_snd)

#print axioms observed_bind_eq_compProd_map
#print axioms observed_restricted_bind_eq_compProd_map
#print axioms observed_normalized_compProd_ac_restricted_bind

end HarmonicBalls
