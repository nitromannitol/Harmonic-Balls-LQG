import HarmonicBalls.Proofs.Sec6.WeightedRootAbsoluteContinuity
import HarmonicBalls.Proofs.Sec6.SingularRootAnnulusRegularity

/-! # Comparison of singular and zero-strength root laws

The imported Section 6 development uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- Absolute continuity of random measures passes to their normalized weighted
root laws, provided the reference region has finite mass almost surely. -/
theorem weightedRestriction_compProd_ac_of_ae_ac
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ ν : Ω → Measure ℂ) (hμ : AEMeasurable μ P) (hν : AEMeasurable ν P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hac : ∀ᵐ ω ∂P, μ ω ≪ ν ω) (hfinite : ∀ᵐ ω ∂P, ν ω B ≠ ∞) :
    P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw ≪
      P ⊗ₘ weightedRestrictionKernel P ν hν B hB (fun _ => 1) measurable_const := by
  let : IsFiniteKernel (weightedRestrictionKernel P ν hν B hB (fun _ => 1)
      measurable_const) := weightedRestrictionKernel_finite P ν _ _ _ _ _
  apply Measure.AbsolutelyContinuous.compProd_right
  filter_upwards [ae_weightedRestrictionKernel_eq P μ hμ B hB w hw,
    ae_weightedRestrictionKernel_eq P ν hν B hB (fun _ => 1) measurable_const,
    hac, hfinite] with ω hwgt hunit hμν hf
  rw [hwgt, hunit, normalizedRestriction, normalizedRestriction]
  change (((μ ω).withDensity w) B)⁻¹ • ((μ ω).withDensity w).restrict B ≪
    (((ν ω).withDensity 1) B)⁻¹ • ((ν ω).withDensity 1).restrict B
  rw [withDensity_one, restrict_withDensity hB]
  exact Measure.smul_absolutelyContinuous.trans
    ((withDensity_absolutelyContinuous _ _).trans
      ((hμν.restrict B).trans
        (Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr hf))))

/-- A weighted root of the singular LQG measure in the unit disk is dominated
by the normalized zero-strength root law for the same whole-plane field. -/
theorem weighted_singular_unitBall_root_ac_zero
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (ball 0 1) measurableSet_ball w hw ≪
    P ⊗ₘ weightedRestrictionKernel P μ₀ (h.aemeasurable_lqgMeasure hμ₀)
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const := by
  apply weightedRestriction_compProd_ac_of_ae_ac
  · exact ae_singular_lqg_absolutelyContinuous_zero hgrowth hγ hγ2 hα h hμ hμ₀
  · filter_upwards [hμ₀] with ω hω
    let : IsLocallyFiniteMeasure (μ₀ ω) := hω.isLocallyFiniteMeasure
    exact measure_ball_ne_top

end HarmonicBalls.Section6
