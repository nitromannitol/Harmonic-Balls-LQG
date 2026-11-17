import HarmonicBalls.Proofs.Potential.BrownianSingularWeightedOccupation

/-! # Singularly weighted Brownian occupation

An integrable envelope bounds singularly dominated occupation weights.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The real part of the singular unit-time occupation. -/
noncomputable def unitSingularOccupationEnvelope (z : ℂ) (q : ℝ)
    (b : ContinuousPath ℂ) : ℝ :=
  (∫⁻ t : ℝ≥0, (ENNReal.ofReal ‖b t - z‖) ^ (-q) ∂(Measure.map Real.toNNReal
    (volume.restrict (Icc (0 : ℝ) 1)))).toReal

/-- The singular occupation envelope is integrable. -/
theorem integrable_unitSingularOccupationEnvelope (x z : ℂ) {q : ℝ}
    (hq0 : 0 < q) (hq2 : q < 2) :
    Integrable (unitSingularOccupationEnvelope z q) (planarBrownianMotion x) := by
  apply integrable_toReal_of_lintegral_ne_top
  · have hf : Measurable (fun p : ContinuousPath ℂ × ℝ≥0 =>
        (ENNReal.ofReal ‖p.1 p.2 - z‖) ^ (-q)) := by fun_prop
    exact (Measurable.lintegral_prod_right hf).aemeasurable
  · exact (planarBrownianMotion_unit_singular_occupation_lt_top x z hq0 hq2).ne

/-- A single occupation envelope controls all singularly dominated weights and submeasures. -/
theorem planarBrownianMotion_ae_unit_singular_weighted_submeasure_integrable
    (x z : ℂ) {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ (g : ℂ → ℝ), Measurable g →
      (∀ y, ENNReal.ofReal |g y| ≤ (ENNReal.ofReal ‖y-z‖) ^ (-q)) →
      ∀ (μ : Measure ℂ), μ ≤ Measure.map (fun t => b t) ν →
        Integrable g μ ∧ (∫ y, |g y| ∂μ) ≤ unitSingularOccupationEnvelope z q b := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [planarBrownianMotion_ae_unit_singular_occupation_lt_top x z hq0 hq2] with b hb
  intro g hg hgq μ hμ
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  have hbm : Measurable b := b.continuous.measurable
  let E : ℝ≥0∞ := ∫⁻ t : ℝ≥0, (ENNReal.ofReal ‖b t - z‖) ^ (-q) ∂ν
  have hlin : (∫⁻ y, ENNReal.ofReal |g y| ∂ρ) ≤ E := by
    rw [show ρ = Measure.map (fun t => b t) ν from rfl,
      lintegral_map hg.abs.ennreal_ofReal hbm]
    exact lintegral_mono fun t => hgq (b t)
  have hfi : Integrable g ρ := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (∫⁻ y, ‖g y‖ₑ ∂ρ) = (∫⁻ y, ENNReal.ofReal |g y| ∂ρ) := by
      apply lintegral_congr
      intro y
      exact Real.enorm_eq_ofReal_abs (g y)
    rw [heq]
    exact lt_of_le_of_lt hlin hb
  have hρ : (∫ y, |g y| ∂ρ) ≤ E.toReal := by
    have h := ENNReal.toReal_mono hb.ne hlin
    rw [← ofReal_integral_eq_lintegral_ofReal hfi.abs
      (Filter.Eventually.of_forall (fun y => abs_nonneg (g y))),
      ENNReal.toReal_ofReal (integral_nonneg (fun y => abs_nonneg (g y)))] at h
    exact h
  refine ⟨hfi.mono_measure hμ, ?_⟩
  exact (integral_mono_measure hμ (Filter.Eventually.of_forall (fun y => abs_nonneg (g y))) hfi.abs).trans hρ

end HarmonicBalls
