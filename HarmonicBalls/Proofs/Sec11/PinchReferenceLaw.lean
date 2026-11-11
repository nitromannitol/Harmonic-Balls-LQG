import HarmonicBalls.Proofs.Sec11.PinchRootedWeight
import Mathlib.MeasureTheory.Measure.Prod

/-! # Reference laws for rooted fields

An independent root and field can be mapped to a shifted field paired with
its root. The comparison with the LQG-rooted law and the local field
absolute continuity are separate inputs, not consequences of this construction.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Law of a shifted field paired with an independent root. -/
noncomputable def shiftedRootReferenceLaw
    {Z Ω F : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] [MeasurableSpace F]
    (ρ : Measure Z) (P : Measure Ω) (shift : Z × Ω → F) : Measure (F × Z) :=
  (ρ.prod P).map (fun x => (shift x, x.1))

/-- A fixed-root almost-sure statement passes to the reference law if, at
almost every root, the shifted field law is absolutely continuous with
respect to the corresponding comparison law. Joint measurability of the
statement and shift is explicit. -/
theorem ae_shiftedRootReferenceLaw_of_ae_comparison
    {Z Ω F : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] [MeasurableSpace F]
    (ρ : Measure Z) (P : Measure Ω) [SFinite P]
    (shift : Z × Ω → F) (hshift : Measurable shift)
    (Q : Z → Measure F) {p : F × Z → Prop}
    (hp : MeasurableSet {x | p x})
    (hac : ∀ᵐ z ∂ρ, P.map (fun ω => shift (z, ω)) ≪ Q z)
    (hfixed : ∀ᵐ z ∂ρ, ∀ᵐ f ∂Q z, p (f, z)) :
    ∀ᵐ x ∂shiftedRootReferenceLaw ρ P shift, p x := by
  have hmap : Measurable (fun x : Z × Ω => (shift x, x.1)) :=
    hshift.prodMk measurable_fst
  apply (ae_map_iff hmap.aemeasurable hp).2
  apply (Measure.ae_prod_iff_ae_ae (hmap hp)).2
  filter_upwards [hac, hfixed] with z hz hfixedz
  have hsection : Measurable (fun ω => shift (z, ω)) :=
    hshift.comp measurable_prodMk_left
  have hsectionp : MeasurableSet {f | p (f, z)} :=
    (measurable_prodMk_right hp)
  exact (ae_map_iff hsection.aemeasurable hsectionp).1 (hz.ae_le hfixedz)

/-- Normalizing the weighted restriction preserves absolute continuity of
the joint rooted law with respect to the unnormalized weighted joint law.
The unnormalized kernel and its almost-sure identification are explicit. -/
theorem weightedRestrictionKernel_compProd_ac_unnormalized
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (η : Kernel Ω ℂ) [IsSFiniteKernel η]
    (hη : ∀ᵐ ω ∂P, η ω = ((μ ω).withDensity w).restrict B) :
    P ⊗ₘ (weightedRestrictionKernel P μ hμ B hB w hw) ≪ P ⊗ₘ η := by
  apply Measure.AbsolutelyContinuous.compProd_right
  filter_upwards [ae_weightedRestrictionKernel_eq P μ hμ B hB w hw, hη] with ω hκ hηω
  rw [hκ, hηω, normalizedRestriction]
  exact Measure.smul_absolutelyContinuous

/-- Fixed-root comparison laws give an almost-everywhere property of the
original random measure, provided the weighted rooted laws are absolutely
continuous with respect to the constructed reference laws. -/
theorem ae_ae_of_shiftedRootReferenceLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (Q : ℕ → ℂ → Measure Ω)
    {p : Ω → ℂ → Prop} (hp : MeasurableSet {x : Ω × ℂ | p x.1 x.2})
    (hrooted : ∀ n, P ⊗ₘ (weightedRestrictionKernel P μ hμ (weightedLocalization w n)
      (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ Q n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂Q n z, p ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p ω z := by
  apply ae_ae_of_rooted_positive_weight P μ hμ hloc w hw hpos hfin
    (fun n => shiftedRootReferenceLaw (ρ n) P (shift n)) hrooted
  intro n
  exact ae_shiftedRootReferenceLaw_of_ae_comparison (ρ n) P (shift n)
    (hshift n) (Q n) hp (hac n) (hfixed n)


end HarmonicBalls
