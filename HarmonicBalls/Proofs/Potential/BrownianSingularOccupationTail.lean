import HarmonicBalls.Proofs.Potential.BrownianSingularOccupation

/-! # Singular occupation near a point

Subcritical inverse-power occupation near a point has a positive power bound.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- Expected unit-time singular occupation near a point decays with the radius. -/
theorem planarBrownianMotion_unit_singular_occupation_tail_le (x z : ℂ) {q p : ℝ}
    (hq : 0 < q) (hqp : q < p) (hp : p < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ δ : ℝ, 0 < δ →
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      (∫⁻ b, ∫⁻ t : ℝ≥0,
        (if ‖b t - z‖ < δ then (ENNReal.ofReal ‖b t - z‖) ^ (-q) else 0) ∂ν
          ∂(planarBrownianMotion x)) ≤ (ENNReal.ofReal δ) ^ (p - q) * C := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let C : ℝ≥0∞ := ∫⁻ b, ∫⁻ t : ℝ≥0, (ENNReal.ofReal ‖b t - z‖) ^ (-p) ∂ν
    ∂(planarBrownianMotion x)
  have hp0 : 0 < p := lt_trans hq hqp
  refine ⟨C, planarBrownianMotion_unit_singular_occupation_lt_top x z hp0 hp, ?_⟩
  intro δ hδ
  have hδ0 : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  have hbound (b : ContinuousPath ℂ) (t : ℝ≥0) :
      (if ‖b t - z‖ < δ then (ENNReal.ofReal ‖b t - z‖) ^ (-q) else 0) ≤
        (ENNReal.ofReal δ) ^ (p - q) * (ENNReal.ofReal ‖b t - z‖) ^ (-p) := by
    split_ifs with h
    · by_cases ha : ENNReal.ofReal ‖b t - z‖ = 0
      · simp [ha, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hp0),
          (ENNReal.rpow_pos_of_nonneg hδ0 (show 0 ≤ p - q by linarith)).ne']
      · have hle : ENNReal.ofReal ‖b t - z‖ ≤ ENNReal.ofReal δ :=
          ENNReal.ofReal_le_ofReal h.le
        have hr := ENNReal.rpow_le_rpow hle (show 0 ≤ p - q by linarith)
        calc
          _ = (ENNReal.ofReal ‖b t - z‖) ^ (-p) *
              (ENNReal.ofReal ‖b t - z‖) ^ (p - q) := by
                rw [← ENNReal.rpow_add _ _ ha ENNReal.ofReal_ne_top]
                congr 1; ring
          _ ≤ (ENNReal.ofReal ‖b t - z‖) ^ (-p) * (ENNReal.ofReal δ) ^ (p - q) :=
            mul_le_mul_right hr _
          _ = _ := mul_comm _ _
    · exact bot_le
  calc
    _ ≤ ∫⁻ b, ∫⁻ t : ℝ≥0, (ENNReal.ofReal δ) ^ (p - q) *
        (ENNReal.ofReal ‖b t - z‖) ^ (-p) ∂ν ∂(planarBrownianMotion x) := by
          exact lintegral_mono fun b => lintegral_mono (hbound b)
    _ = ∫⁻ b, (ENNReal.ofReal δ) ^ (p - q) *
        (∫⁻ t : ℝ≥0, (ENNReal.ofReal ‖b t - z‖) ^ (-p) ∂ν) ∂(planarBrownianMotion x) := by
      congr 1; funext b
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)]
    _ = (ENNReal.ofReal δ) ^ (p - q) * C := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)]

end HarmonicBalls
