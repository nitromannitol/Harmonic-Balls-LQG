import HarmonicBalls.Proofs.Sec6.CollarFailureFrequency
import HarmonicBalls.Proofs.Sec6.SizeRatioTranslationLaw

/-! # Recentring and rescaling relative collar events

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- The centred collar event of the translated measure is the corresponding
collar event around the original centre. -/
theorem relativeCollarFailure_map_sub (μ : Measure ℂ) (z : ℂ) (r η : ℝ)
    (d : ℝ≥0∞) :
    RelativeCollarFailure (μ.map (fun x : ℂ => x-z)) r η d ↔
      d * μ (annulus z (3*r) (5*r)) <
        μ (annulus z (3*r-η*r) (5*r+η*r) \
          annulus z (3*r+η*r) (5*r-η*r)) := by
  unfold RelativeCollarFailure
  rw [map_sub_annulus]
  have hm : MeasurableSet (annulus (0 : ℂ) (3*r-η*r) (5*r+η*r) \
      annulus 0 (3*r+η*r) (5*r-η*r)) :=
    (measurableSet_ball.diff measurableSet_closedBall).diff
      (measurableSet_ball.diff measurableSet_closedBall)
  have ha (a b : ℝ) : (fun x : ℂ => x-z) ⁻¹' annulus 0 a b = annulus z a b := by
    ext x
    simp [annulus, mem_ball, mem_closedBall, dist_eq_norm]
  rw [Measure.map_apply (by fun_prop) hm, preimage_sdiff, ha, ha]

/-- Recentring, dilating by the inverse scale, and multiplying by any positive
finite mass factor transports relative collar failure to unit scale. -/
theorem relativeCollarFailure_recenter_rescale
    (μ : Measure ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r) (η : ℝ)
    (d t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    RelativeCollarFailure
      (t • ((μ.map (fun x : ℂ => x-z)).map (fun x : ℂ => r⁻¹ • x))) 1 η d ↔
    d * μ (annulus z (3*r) (5*r)) <
      μ (annulus z (3*r-η*r) (5*r+η*r) \
        annulus z (3*r+η*r) (5*r-η*r)) := by
  rw [relativeCollarFailure_smul _ _ _ _ _ ht htop,
    relativeCollarFailure_map_inv_smul _ hr]
  simpa only [mul_one] using relativeCollarFailure_map_sub μ z r η d

/-- The recentered and rescaled measure is jointly measurable in a measurable
locally finite random measure and its centre. -/
theorem measurable_recenter_rescale_measure
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ)
    (hμ : Measurable μ) (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω)) (r : ℝ) :
    Measurable (fun p : Ω × ℂ =>
      ((μ p.1).map (fun x : ℂ => x-p.2)).map (fun x : ℂ => r⁻¹ • x)) := by
  have hm := measurable_map_of_locallyFinite (hμ.comp measurable_fst)
    (fun p => hloc p.1)
    (f := fun p : (Ω × ℂ) × ℂ => r⁻¹ • (p.2-p.1.2)) (by fun_prop)
  convert hm using 1
  funext p
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A measurable finite-mass normalization may be included in the recentered
measure without losing joint measurability. -/
theorem measurable_normalized_recenter_rescale_measure
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ)
    (hμ : Measurable μ) (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω)) (r : ℝ)
    (t : Ω × ℂ → ℝ≥0∞) (ht : Measurable t) :
    Measurable (fun p : Ω × ℂ => t p •
      ((μ p.1).map (fun x : ℂ => x-p.2)).map (fun x : ℂ => r⁻¹ • x)) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [Measure.smul_apply, smul_eq_mul]
  exact Measurable.mul ht ((Measure.measurable_coe hA).comp
    (measurable_recenter_rescale_measure μ hμ hloc r))

end HarmonicBalls.Section6
