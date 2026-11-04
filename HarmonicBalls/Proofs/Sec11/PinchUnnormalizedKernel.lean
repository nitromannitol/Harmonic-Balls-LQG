import HarmonicBalls.Proofs.Sec11.PinchReferenceLaw
import Mathlib.Probability.Kernel.WithDensity

/-! # Unnormalized weighted sampling kernels

Recover the weighted restriction from the normalized sampling kernel by
multiplying by its finite total mass. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-- A finite representative of the weighted mass. Infinite mass is sent to
zero; this does not affect the almost-sure identification when mass is finite. -/
noncomputable def weightedRestrictionMass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (w : ℂ → ℝ≥0∞) : Ω → ℝ≥0∞ :=
  fun ω => ENNReal.ofReal ((((hμ.mk μ) ω).withDensity w) B).toReal

/-- The unnormalized weighted restriction, represented by a density on the
normalized sampling kernel. -/
noncomputable def unnormalizedWeightedRestrictionKernel
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    Kernel Ω ℂ :=
  (weightedRestrictionKernel P μ hμ B hB w hw).withDensity
    (fun ω _ => weightedRestrictionMass P μ hμ B w ω)

instance unnormalizedWeightedRestrictionKernel_sfinite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    IsSFiniteKernel (unnormalizedWeightedRestrictionKernel P μ hμ B hB w hw) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

theorem ae_unnormalizedWeightedRestrictionKernel_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hfin : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ ∞) :
    ∀ᵐ ω ∂P, unnormalizedWeightedRestrictionKernel P μ hμ B hB w hw ω =
      ((μ ω).withDensity w).restrict B := by
  have hmass : Measurable (weightedRestrictionMass P μ hμ B w) := by
    exact (((Measure.measurable_coe hB).comp
      ((measurable_measure_withDensity w hw).comp hμ.measurable_mk)).ennreal_toReal).ennreal_ofReal
  have hmass' : Measurable (Function.uncurry (fun ω (_ : ℂ) =>
      weightedRestrictionMass P μ hμ B w ω)) := hmass.comp measurable_fst
  filter_upwards [hμ.ae_eq_mk, ae_weightedRestrictionKernel_eq P μ hμ B hB w hw, hfin]
    with ω hω hκ hfinite
  rw [unnormalizedWeightedRestrictionKernel, Kernel.withDensity_apply _ hmass',
    withDensity_const, hκ]
  have hmassval : weightedRestrictionMass P μ hμ B w ω = ((μ ω).withDensity w) B := by
    simp only [weightedRestrictionMass, ← hω, ENNReal.ofReal_toReal hfinite]
  rw [hmassval, normalizedRestriction, smul_smul]
  by_cases hz : ((μ ω).withDensity w) B = 0
  · have hzero : ((μ ω).withDensity w).restrict B = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      simpa using hz
    simp [hzero]
  · rw [ENNReal.mul_inv_cancel hz hfinite, one_smul]

/-- Normalizing the weighted restriction preserves absolute continuity of
the rooted joint law, using the canonical unnormalized kernel. -/
theorem weightedRestrictionKernel_compProd_ac_canonical
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hfin : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ ∞) :
    P ⊗ₘ (weightedRestrictionKernel P μ hμ B hB w hw) ≪
      P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ B hB w hw) :=
  weightedRestrictionKernel_compProd_ac_unnormalized P μ hμ B hB w hw _
    (ae_unnormalizedWeightedRestrictionKernel_eq P μ hμ B hB w hw hfin)

/-- The rooted transfer can use comparison of the unnormalized joint law;
local finiteness supplies the mass condition for each localization. -/
theorem ae_ae_of_unnormalized_shiftedRootReferenceLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (Q : ℕ → ℂ → Measure Ω)
    {p : Ω → ℂ → Prop} (hp : MeasurableSet {x : Ω × ℂ | p x.1 x.2})
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ Q n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂Q n z, p ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p ω z := by
  apply ae_ae_of_shiftedRootReferenceLaw P μ hμ hloc w hw hpos hfin ρ shift hshift Q hp
  · intro n
    have hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity w) (weightedLocalization w n) ≠ ∞ := by
      filter_upwards [hloc] with ω hω
      let : IsLocallyFiniteMeasure (μ ω) := hω
      exact weightedLocalization_measure_ne_top (μ ω) hw n
    exact (weightedRestrictionKernel_compProd_ac_canonical P μ hμ _
      (measurableSet_weightedLocalization hw n) w hw hmass).trans (hrooted n)
  · exact hac
  · exact hfixed

#print axioms ae_ae_of_unnormalized_shiftedRootReferenceLaw
#print axioms ae_unnormalizedWeightedRestrictionKernel_eq
#print axioms weightedRestrictionKernel_compProd_ac_canonical

end HarmonicBalls
