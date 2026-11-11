import HarmonicBalls.Proofs.Sec8.RootedCircleMeasurableVersion
import HarmonicBalls.Proofs.Sec8.RootedSamplingEquivalence

/-! # Normalization of rooted circle observation laws

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- The laws of a local observation and a translated centered circle under
normalized and unnormalized weighted sampling are mutually absolutely
continuous. No positivity of the sampled mass is required. -/
theorem IsWholePlaneGFF.rooted_centeredCircle_laws_mutually_absolutelyContinuous
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {γ α : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hm : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hfin : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ ∞)
    (Y : Ω × ℂ → E) (hY : Measurable Y) (n : ℕ) (z : ℂ) :
    (P ⊗ₘ weightedRestrictionKernel P μ hm B hB w hw).map (fun x => (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2)) ≪
    (P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hm B hB w hw).map (fun x => (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2)) ∧
    (P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hm B hB w hw).map (fun x => (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2)) ≪
    (P ⊗ₘ weightedRestrictionKernel P μ hm B hB w hw).map (fun x => (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2)) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let K := weightedRestrictionKernel P μ hm B hB w hw
  let L := unnormalizedWeightedRestrictionKernel P μ hm B hB w hw
  obtain ⟨g, hgm, hgeq⟩ := hGFF.exists_rooted_circle_measurable_version hμ hm B hB w hw
  let f : Ω × ℂ → E × ℝ := fun x => (Y x, g x (dyadicScale n) z - g x (dyadicScale n) 0)
  have hpoint (v : ℂ) : Measurable (fun x => g x (dyadicScale n) v) :=
    (hgm n).comp (measurable_id.prodMk measurable_const)
  have hf : Measurable f := hY.prodMk ((hpoint z).sub (hpoint 0))
  have heq : ∀ᵐ x ∂(P ⊗ₘ K), f x = (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2) := by
    filter_upwards [hgeq] with x hx
    simp only [f, hx.1 n z, hx.1 n 0, zero_add]
  have heq' : ∀ᵐ x ∂(P ⊗ₘ L), f x = (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2) :=
    (ae_weightedRestriction_compProd_iff P μ hm B hB w hw hfin _).1 heq
  have hac : (P ⊗ₘ K).map f ≪ (P ⊗ₘ L).map f :=
    (weightedRestrictionKernel_compProd_ac_canonical P μ hm B hB w hw hfin).map hf
  have hca : (P ⊗ₘ L).map f ≪ (P ⊗ₘ K).map f :=
    (unnormalizedWeightedRestrictionKernel_compProd_ac_normalized P μ hm B hB w hw hfin).map hf
  rw [Measure.map_congr heq, Measure.map_congr heq'] at hac hca
  exact ⟨hac, hca⟩

end HarmonicBalls
