import HarmonicBalls.Steps.Sec11.LocalExtremaRepresentatives
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable
import HarmonicBalls.Proofs.Sec5.LocalMeasureEvaluations

/-! # Local representatives of the annular Green potential -/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open scoped ENNReal

/-- The annular Green-potential supremum is determined locally by the LQG
measure, under the staged measure-locality hypothesis. -/
theorem exists_local_annulusGreenPotentialSup_representative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) (z : ℂ) (a b : ℝ) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC (ball z b)] Y ∧
      ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) z a b = Y ω := by
  let V := ball z b
  let A := annulus z a b
  let m := fieldSigmaAlgebra α₀ hC V
  let K : A → ℂ → ℝ≥0∞ := fun x y =>
    if y = x then ∞ else ENNReal.ofReal (greenFunction V x y)
  have hAmeas : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hAV : A ⊆ V := sdiff_subset
  have hK (x : A) : Measurable (K x) := by
    exact Measurable.ite (measurableSet_singleton (x : ℂ)) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  have hsections (x : A) : ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, (∫⁻ y in A, K x y ∂(μ ω)) = Y ω := by
    refine @exists_local_lintegral_representative Ω ℂ mΩ inferInstance P m
      (fun ω => (μ ω).restrict A) (K x) (hK x) ?_
    intro B hB
    obtain ⟨Y, hY, hYeq⟩ := @exists_local_lqg_borel_mass_representative Ω mΩ P γ α₀ hC hcirc μ hγ hγ₂ hα
      hgff hμ hloc V isOpen_ball isBounded_ball (B ∩ A) (hB.inter hAmeas)
    refine ⟨Y, hY, ?_⟩
    filter_upwards [hYeq] with ω hω
    simpa only [Measure.restrict_apply hB, inter_assoc, inter_eq_self_of_subset_left hAV] using hω
  choose G hG hEq using hsections
  let F : Ω → A → ℝ≥0∞ := fun ω x => ∫⁻ y in A, K x y ∂(μ ω)
  have hsc : ∀ ω, LowerSemicontinuous (F ω) := by
    intro ω
    apply lowerSemicontinuous_lintegral_of_sections
    · exact hK
    · intro y
      have hc := (continuousOn_extendedGreenKernel_ball_centered z b y).mono hAV
      exact (continuousOn_iff_continuous_domRestrict.mp hc).lowerSemicontinuous
  obtain ⟨Y, hY, hYeq⟩ :=
    @exists_measurable_iSup_representative_of_lowerSemicontinuous Ω A mΩ inferInstance
      inferInstance P m F (fun ω x => G x ω) hG hEq (Filter.Eventually.of_forall hsc)
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hYeq] with ω hω
  simpa only [annulusGreenPotentialSup, F, K, V, A, iSup_subtype] using hω

end HarmonicBalls
