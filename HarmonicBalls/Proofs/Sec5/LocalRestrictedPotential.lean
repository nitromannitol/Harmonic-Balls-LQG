import HarmonicBalls.Proofs.Sec5.LocalMeasureEvaluations
import HarmonicBalls.Proofs.Sec9.DominatedGreenPotential

/-! # Field-local potential of a restricted LQG measure

The disc Green potential of the restriction to an open set has a representative
measurable with respect to the field on that set. Its continuity follows from
domination by the original measure; lower volume growth need not survive the
restriction.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace

universe u

/-- Each section of the Green potential of a restricted LQG measure has a
field-local representative. The open set need not be bounded. -/
theorem exists_local_lqg_restricted_greenPotentialBall_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (R : ℝ) (x : ℂ) :
    ∃ Y : Ω → ℝ, Measurable[fieldSigmaAlgebra α₀ hC U] Y ∧
      ∀ᵐ ω ∂P, greenPotentialBall ((μ ω).restrict U) R x = Y ω := by
  have hg := measurable_greenFunction_ball R x
  let V : Set ℂ := U ∩ ball 0 R
  have hV : IsOpen V := hU.inter isOpen_ball
  have hVb : Bornology.IsBounded V := isBounded_ball.subset inter_subset_right
  have hVsub : V ⊆ U := inter_subset_left
  obtain ⟨Y, hY, hYeq⟩ := exists_local_lintegral_representative P
    (fieldSigmaAlgebra α₀ hC U) (fun ω => (μ ω).restrict V)
    (fun y => ENNReal.ofReal (greenFunction (ball 0 R) x y))
    (ENNReal.measurable_ofReal.comp hg) (by
      intro A hA
      obtain ⟨Y, hY, hYeq⟩ := exists_local_lqg_borel_mass_representative hγ hγ2 hα
        hGFF hμ hloc hV hVb A hA
      refine ⟨Y, hY.mono (fieldSigmaAlgebra_mono α₀ hC hVsub) le_rfl, ?_⟩
      filter_upwards [hYeq] with ω hω
      simpa only [Measure.restrict_apply hA] using hω)
  refine ⟨fun ω => (Y ω).toReal, ENNReal.measurable_toReal.comp hY, ?_⟩
  filter_upwards [hYeq] with ω hω
  have hrestrict : ((μ ω).restrict U).restrict (ball 0 R) = (μ ω).restrict V := by
    rw [Measure.restrict_restrict measurableSet_ball, inter_comm]
  have heq : greenPotentialBall ((μ ω).restrict U) R x =
      ∫ y, greenFunction (ball 0 R) x y ∂((μ ω).restrict V) := by
    unfold greenPotentialBall
    rw [hrestrict]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => greenFunction_ball_comm R y x)
  rw [heq, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (greenFunction_nonneg isBounded_ball x)) hg.aestronglyMeasurable, hω]

/-- A locally finite measure with volume growth dominates restrictions whose
Green potentials are continuous on the closed disc. -/
theorem continuousOn_greenPotentialBall_restrict_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U : Set ℂ}
    {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) :
    ContinuousOn (greenPotentialBall (μ.restrict U) R) (closedBall 0 R) := by
  have heq : greenPotentialBall ((μ.restrict U).restrict (ball 0 R)) R =
      greenPotentialBall (μ.restrict U) R := by
    funext x
    unfold greenPotentialBall
    rw [Measure.restrict_restrict measurableSet_ball, inter_self]
  rw [← heq]
  exact (dominated_greenPotentialBall hμ hR hV Measure.restrict_le_self).1

/-- The entire continuous Green potential of a restricted LQG measure admits
a representative measurable with respect to the field on the restricting set. -/
theorem exists_local_lqg_restricted_greenPotentialBall_continuous_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} (hR : 0 < R) :
    ∃ Q : Ω → C(closedBall (0 : ℂ) R, ℝ),
      Measurable[fieldSigmaAlgebra α₀ hC U] Q ∧
      ∀ᵐ ω ∂P, ∀ x, Q ω x = greenPotentialBall ((μ ω).restrict U) R x := by
  classical
  let X := closedBall (0 : ℂ) R
  let : Nonempty X := ⟨⟨0, by change (0 : ℂ) ∈ closedBall 0 R; simpa using hR.le⟩⟩
  let e : ℕ → X := denseSeq X
  let enc : C(X, ℝ) → ℕ → ℝ := fun f n => f (e n)
  have henc : Measurable enc := by
    apply Measurable.of_eval
    intro n
    exact ContinuousMap.measurable_eval (e n)
  have hinj : Function.Injective enc := by
    intro f g hfg
    apply ContinuousMap.ext
    intro x
    have hfun : (f : X → ℝ) = g := (denseRange_denseSeq X).equalizer f.continuous g.continuous (by
      funext n
      exact congrFun hfg n)
    exact congrFun hfun x
  have hemb : MeasurableEmbedding enc := henc.measurableEmbedding hinj
  choose Y hY hYeq using fun n : ℕ =>
    exists_local_lqg_restricted_greenPotentialBall_representative hγ hγ2 hα hGFF hμ hloc hU R (e n)
  let q : Ω → ℕ → ℝ := fun ω n => Y n ω
  have hq : Measurable[fieldSigmaAlgebra α₀ hC U] q := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    exact Measurable.of_eval hY
  refine ⟨fun ω => hemb.invFun (q ω), hemb.measurable_invFun.comp hq, ?_⟩
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae, ae_all_iff.mpr hYeq] with ω hω heq
  have hc := continuousOn_greenPotentialBall_restrict_of_volumeGrowth (U := U) hω.1 hR (hω.2 R hR)
  let f : C(X, ℝ) := ⟨fun x => greenPotentialBall ((μ ω).restrict U) R x, hc.domRestrict⟩
  have hqeq : q ω = enc f := by
    funext n
    exact (heq n).symm
  intro x
  change hemb.invFun (q ω) x = _
  rw [hqeq, hemb.leftInverse_invFun f]
  rfl

end HarmonicBalls
