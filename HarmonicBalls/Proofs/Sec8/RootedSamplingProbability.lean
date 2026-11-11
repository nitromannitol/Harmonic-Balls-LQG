import HarmonicBalls.Proofs.Sec8.CommonContinuityApproximation
import HarmonicBalls.Proofs.Sec11.PinchRootedKernel

/-! # Probability law of a normalized root

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- An almost-everywhere property of the field holds under any composition
product with a sampling kernel. -/
theorem ae_fst_of_ae_compProd
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) (κ : Kernel Ω Z) {p : Ω → Prop} (hp : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ x ∂(P ⊗ₘ κ), p x.1 := by
  obtain ⟨s, hs, hsm, hsz⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  have hs' : ∀ᵐ ω ∂P, ω ∉ s := ae_iff.mpr (by simpa using hsz)
  have ht := Measure.ae_compProd_of_ae_fst κ hsm.compl hs'
  filter_upwards [ht] with x hx
  by_contra hn
  exact hx (hs hn)

/-- If the sampling set has positive finite weighted mass almost surely,
the normalized weighted rooted law is a probability measure. -/
theorem isProbabilityMeasure_weightedRestriction_compProd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞) :
    IsProbabilityMeasure (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw) := by
  let κ := weightedRestrictionKernel P μ hμ B hB w hw
  have hk : ∀ᵐ ω ∂P, κ ω univ = 1 := by
    filter_upwards [ae_weightedRestrictionKernel_eq P μ hμ B hB w hw, hmass] with ω he hm
    rw [he]
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hm.1 hm.2
  refine ⟨?_⟩
  rw [Measure.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  rw [lintegral_congr_ae hk]
  simp

/-- Under a normalized rooted law, the random recentered measure remains
almost everywhere measurable and locally finite. -/
theorem aemeasurable_recentered_of_weightedRestriction_compProd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    AEMeasurable (fun x : Ω × ℂ => (μ x.1).map (fun v : ℂ => v - x.2))
        (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw) ∧
      ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw),
        IsLocallyFiniteMeasure ((μ x.1).map (fun v : ℂ => v - x.2)) := by
  let κ := weightedRestrictionKernel P μ hμ B hB w hw
  obtain ⟨F, hF, hFeq⟩ := exists_jointlyMeasurable_centeredMeasure P hμ hloc
  have hF' : Measurable (fun x : Ω × ℂ => (F (x.2, x.1)).val) :=
    measurable_subtype_coe.comp (hF.comp (measurable_snd.prodMk measurable_fst))
  have heq : ∀ᵐ x ∂(P ⊗ₘ κ),
      (μ x.1).map (fun v : ℂ => v - x.2) = (F (x.2, x.1)).val := by
    filter_upwards [ae_fst_of_ae_compProd P κ hFeq] with x hx
    exact hx x.2
  constructor
  · apply hF'.aemeasurable.congr
    filter_upwards [heq] with x hx
    exact hx.symm
  · filter_upwards [heq] with x hx
    rw [hx]
    exact (F (x.2, x.1)).property

end HarmonicBalls
