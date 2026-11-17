import HarmonicBalls.Proofs.Potential.BrownianUniformBallOccupation
import HarmonicBalls.Proofs.Potential.BrownianOccupationRieszEnergy

/-! # Shifted Gaussian inverse moments

Inverse moments of a planar Gaussian are bounded uniformly over shifts.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The inverse moment of a standard planar Gaussian is bounded uniformly over shifts. -/
theorem lintegral_stdPlanarGaussian_shift_enorm_rpow_neg_le (z : ℂ) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 2) :
    (∫⁻ w, (ENNReal.ofReal ‖w - z‖) ^ (-a) ∂stdPlanarGaussian) ≤
      ENNReal.ofReal (1 + (4 / Real.sqrt (2 * Real.pi)) ^ 2 * (a / (2 - a))) := by
  let A : ℝ := (4 / Real.sqrt (2 * Real.pi)) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hball : ∀ r : ℝ, 0 < r →
      stdPlanarGaussian (closedBall z r) ≤ ENNReal.ofReal (A * r ^ (2 : ℝ)) := by
    intro r hr
    have hsub : closedBall z r ⊆ ball z (2 * r) := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      linarith
    calc
      _ ≤ stdPlanarGaussian (ball z (2 * r)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (2 * (2 * r) / Real.sqrt (2 * Real.pi * (1 : ℝ≥0))) ^ 2 :=
        planarGaussian_ball_le_uniform_center (v := 1) (by norm_num) z (by positivity)
      _ = ENNReal.ofReal (A * r ^ (2 : ℝ)) := by
        rw [← ENNReal.ofReal_pow (by positivity)]
        congr 1
        rw [Real.rpow_two]
        dsimp [A]
        ring_nf
  have hz : stdPlanarGaussian {z} = 0 :=
    measure_singleton_eq_zero_of_le_rpow (by norm_num : (0 : ℝ) < 2) hball
  have hae : ∀ᵐ w ∂stdPlanarGaussian, w ≠ z := by
    simpa using (measure_eq_zero_iff_ae_notMem.mp hz)
  have heq : (∫⁻ w, (ENNReal.ofReal ‖w - z‖) ^ (-a) ∂stdPlanarGaussian) =
      ∫⁻ w, ENNReal.ofReal (‖z - w‖ ^ (-a)) ∂stdPlanarGaussian := by
    apply lintegral_congr_ae
    filter_upwards [hae] with w hw
    rw [ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hw))]
    simp only [norm_sub_rev]
  rw [heq]
  simpa only [A] using (lintegral_norm_sub_rpow_neg_le (ν := stdPlanarGaussian)
    (x := z) (m := 1) (A := A) (α := a) (β := 2) ha ha2 (by norm_num) hA
    (by simp [stdPlanarGaussian]) hball)

end HarmonicBalls
