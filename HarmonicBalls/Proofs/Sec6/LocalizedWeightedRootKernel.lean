import HarmonicBalls.Proofs.Sec6.LocalizedSingularRootCounts
import HarmonicBalls.Proofs.Sec6.RootedMassTypicalEventTransfer

/-! # Localized weighted sampling kernels

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- Weighted restriction is absolutely continuous with respect to the original
measure and the sampled root belongs to the restriction set almost surely. -/
theorem weightedRestrictionKernel_ac_and_ae_mem
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    (∀ᵐ ω ∂P, weightedRestrictionKernel P μ hμ B hB w hw ω ≪ μ ω) ∧
    (∀ᵐ p ∂(P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw), p.2 ∈ B) := by
  constructor
  · filter_upwards [ae_weightedRestrictionKernel_eq P μ hμ B hB w hw] with ω he
    rw [he, normalizedRestriction]
    exact Measure.smul_absolutelyContinuous.trans
      (Measure.absolutelyContinuous_restrict.trans (withDensity_absolutelyContinuous _ _))
  · apply Measure.ae_compProd_of_ae_ae (hB.preimage measurable_snd)
    filter_upwards [ae_weightedRestrictionKernel_eq P μ hμ B hB w hw] with ω he
    rw [he, normalizedRestriction]
    exact Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem hB)

/-- Sampling from a weighted restriction to the middle annulus supplies the
localization and absolute-continuity hypotheses of the singular count bound. -/
theorem weightedRestrictionKernel_middle_annulus
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (x₀ : ℂ) (ρ : ℝ) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    (∀ᵐ ω ∂P, weightedRestrictionKernel P μ hμ (annulus x₀ (ρ/2) ρ)
      (measurableSet_ball.diff measurableSet_closedBall) w hw ω ≪ μ ω) ∧
    (∀ᵐ p ∂(P ⊗ₘ weightedRestrictionKernel P μ hμ (annulus x₀ (ρ/2) ρ)
      (measurableSet_ball.diff measurableSet_closedBall) w hw), p.2 ∈ annulus x₀ (ρ/2) ρ) :=
  weightedRestrictionKernel_ac_and_ae_mem P μ hμ _ _ w hw

/-- The weighted restriction kernel has total mass one whenever its weighted
mass on the restriction set is positive and finite. -/
theorem ae_weightedRestrictionKernel_normalized
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞) :
    ∀ᵐ ω ∂P, weightedRestrictionKernel P μ hμ B hB w hw ω univ = 1 := by
  filter_upwards [ae_weightedRestrictionKernel_eq P μ hμ B hB w hw, hmass] with ω he hm
  rw [he]
  simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hm.1 hm.2

end HarmonicBalls.Section6
