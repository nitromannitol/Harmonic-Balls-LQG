import HarmonicBalls.Proofs.Sec8.RootedSamplingProbability
import HarmonicBalls.Proofs.Sec11.PinchUnnormalizedKernel

/-! # Normalized and unnormalized rooted laws

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Finite weighted mass makes the unnormalized rooted law absolutely
continuous with respect to the normalized rooted law, even on zero-mass
samples. -/
theorem unnormalizedWeightedRestrictionKernel_compProd_ac_normalized
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hfin : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ ∞) :
    P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ B hB w hw) ≪
      P ⊗ₘ (weightedRestrictionKernel P μ hμ B hB w hw) := by
  apply Measure.AbsolutelyContinuous.compProd_right
  filter_upwards [ae_unnormalizedWeightedRestrictionKernel_eq P μ hμ B hB w hw hfin,
    ae_weightedRestrictionKernel_eq P μ hμ B hB w hw, hfin] with ω hU hN hω
  rw [hU, hN]
  by_cases hz : ((μ ω).withDensity w) B = 0
  · have hzero : ((μ ω).withDensity w).restrict B = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      simpa using hz
    rw [hzero]
    exact Measure.AbsolutelyContinuous.zero _
  · rw [restrict_eq_smul_normalizedRestriction ((μ ω).withDensity w) hB hz hω]
    exact Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict

/-- Normalized and unnormalized weighted root laws have exactly the same
almost-everywhere properties when their weighted mass is finite. -/
theorem ae_weightedRestriction_compProd_iff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hfin : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ ∞) (p : Ω × ℂ → Prop) :
    (∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw), p x) ↔
      ∀ᵐ x ∂(P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hμ B hB w hw), p x := by
  constructor
  · intro h
    exact (unnormalizedWeightedRestrictionKernel_compProd_ac_normalized P μ hμ B hB w hw hfin).ae_le h
  · intro h
    exact (weightedRestrictionKernel_compProd_ac_canonical P μ hμ B hB w hw hfin).ae_le h

#print axioms unnormalizedWeightedRestrictionKernel_compProd_ac_normalized
#print axioms ae_weightedRestriction_compProd_iff

end HarmonicBalls
