import HarmonicBalls.Proofs.Sec6.WeightedSingularRootCounts

/-! # Normalized singular-mass roots in an annulus

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- A nonempty middle annulus has positive finite singular LQG mass under
all-scales volume growth. -/
theorem ae_singular_lqg_middle_annulus_pos_finite
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (x₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, 0 < μ ω (annulus x₀ (ρ/2) ρ) ∧
      μ ω (annulus x₀ (ρ/2) ρ) ≠ ∞ := by
  have hne : (annulus x₀ (ρ/2) ρ).Nonempty := by
    refine ⟨x₀ + (((3*ρ/4 : ℝ) : ℂ)), ?_⟩
    have hd : dist (x₀ + (((3*ρ/4 : ℝ) : ℂ))) x₀ = 3*ρ/4 := by
      simp [dist_eq_norm, show 0 ≤ ρ by positivity]
    change dist (x₀ + (((3*ρ/4 : ℝ) : ℂ))) x₀ < ρ ∧
      ¬ dist (x₀ + (((3*ρ/4 : ℝ) : ℂ))) x₀ ≤ ρ/2
    rw [hd]
    constructor <;> linarith
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα h hμ
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ2 hα
    Ω P hC hcirc μ h hμ
  filter_upwards [hV, hfull] with ω hloc hf
  let : IsLocallyFiniteMeasure (μ ω) := hloc.1
  refine ⟨hf _ (isOpen_ball.sdiff isClosed_closedBall) hne, ?_⟩
  exact ne_top_of_le_ne_top (measure_ball_lt_top (μ := μ ω) (x := x₀) (r := ρ)).ne
    (measure_mono sdiff_subset)

/-- The unit-weight restriction kernel is normalized on a positive-radius
middle annulus. -/
theorem ae_singular_lqg_middle_annulus_kernel_normalized
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (x₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall)
      (fun _ => 1) measurable_const ω univ = 1 := by
  apply ae_weightedRestrictionKernel_normalized
  filter_upwards [ae_singular_lqg_middle_annulus_pos_finite hgrowth hγ hγ2 hα h hμ x₀ hρ] with ω hm
  change ((μ ω).withDensity 1) (annulus x₀ (ρ/2) ρ) ≠ 0 ∧
    ((μ ω).withDensity 1) (annulus x₀ (ρ/2) ρ) ≠ ∞
  rw [withDensity_one]
  exact ⟨hm.1.ne', hm.2⟩

/-- Projecting the normalized middle-annulus rooted law onto the field
coordinate recovers the original field law. -/
theorem measurePreserving_fst_singular_lqg_middle_annulus
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (x₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    MeasurePreserving Prod.fst
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall)
        (fun _ => 1) measurable_const) P := by
  let : IsFiniteKernel (weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall)
      (fun _ => 1) measurable_const) := weightedRestrictionKernel_finite P μ _ _ _ _ _
  exact measurePreserving_fst_compProd_of_ae_normalized P
    (weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall)
      (fun _ => 1) measurable_const)
    (ae_singular_lqg_middle_annulus_kernel_normalized hgrowth hγ hγ2 hα h hμ x₀ hρ)

end HarmonicBalls.Section6
