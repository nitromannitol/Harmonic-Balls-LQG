import HarmonicBalls.Proofs.Sec6.LocalizedSingularRootNormalization

/-! # Absolute continuity of weighted annulus roots

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- A weighted normalized restriction is absolutely continuous with respect to
unit-weight normalized restriction on the same set, when its unweighted mass
is finite. No positivity assumption on the weight is needed. -/
theorem ae_weightedRestrictionKernel_ac_unit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hfinite : ∀ᵐ ω ∂P, μ ω B ≠ ∞) :
    ∀ᵐ ω ∂P, weightedRestrictionKernel P μ hμ B hB w hw ω ≪
      weightedRestrictionKernel P μ hμ B hB (fun _ => 1) measurable_const ω := by
  filter_upwards [ae_weightedRestrictionKernel_eq P μ hμ B hB w hw,
    ae_weightedRestrictionKernel_eq P μ hμ B hB (fun _ => 1) measurable_const,
    hfinite] with ω hwgt hunit hf
  rw [hwgt, hunit, normalizedRestriction, normalizedRestriction]
  change (((μ ω).withDensity w) B)⁻¹ • ((μ ω).withDensity w).restrict B ≪
    (((μ ω).withDensity 1) B)⁻¹ • ((μ ω).withDensity 1).restrict B
  rw [withDensity_one, restrict_withDensity hB]
  exact Measure.smul_absolutelyContinuous.trans
    ((withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr hf)))

/-- Weighted and unit-weight rooted laws on the same finite-mass set have
absolutely continuous composition products. -/
theorem weightedRestriction_compProd_ac_unit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hfinite : ∀ᵐ ω ∂P, μ ω B ≠ ∞) :
    P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw ≪
      P ⊗ₘ weightedRestrictionKernel P μ hμ B hB (fun _ => 1) measurable_const := by
  let : IsFiniteKernel (weightedRestrictionKernel P μ hμ B hB (fun _ => 1)
      measurable_const) := weightedRestrictionKernel_finite P μ _ _ _ _ _
  exact Measure.AbsolutelyContinuous.compProd_right
    (ae_weightedRestrictionKernel_ac_unit P μ hμ B hB w hw hfinite)

/-- A weighted singular LQG middle-annulus root law is absolutely continuous
with respect to the corresponding unit-weight singular root law. -/
theorem weighted_singular_middleAnnulus_root_ac_unit
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (x₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall) w hw ≪
    P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall)
      (fun _ => 1) measurable_const := by
  apply weightedRestriction_compProd_ac_unit
  exact (ae_singular_lqg_middle_annulus_pos_finite hgrowth hγ hγ2 hα h hμ x₀ hρ).mono
    fun _ hm => hm.2

end HarmonicBalls.Section6
