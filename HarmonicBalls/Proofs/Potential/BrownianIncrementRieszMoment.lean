import HarmonicBalls.Proofs.Potential.BrownianOccupationRieszEnergy

/-! # Inverse moments of planar Gaussian increments

A standard planar Gaussian has finite inverse-power moments below dimension two.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- A standard planar Gaussian has a finite inverse-power moment below dimension two. -/
theorem lintegral_stdPlanarGaussian_enorm_rpow_neg_lt_top {a : ℝ}
    (ha : 0 < a) (ha2 : a < 2) :
    (∫⁻ z, (ENNReal.ofReal ‖z‖) ^ (-a) ∂stdPlanarGaussian) < ∞ := by
  let A : ℝ := (4 / Real.sqrt (2 * Real.pi)) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hball : ∀ r : ℝ, 0 < r →
      stdPlanarGaussian (closedBall 0 r) ≤ ENNReal.ofReal (A * r ^ (2 : ℝ)) := by
    intro r hr
    have hsub : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := by
      intro z hz
      rw [mem_closedBall] at hz
      rw [mem_ball]
      linarith
    calc
      _ ≤ stdPlanarGaussian (ball 0 (2 * r)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (2 * (2 * r) / Real.sqrt (2 * Real.pi * (1 : ℝ≥0))) ^ 2 :=
        planarGaussian_ball_le (v := 1) (by norm_num) (by positivity)
      _ = ENNReal.ofReal (A * r ^ (2 : ℝ)) := by
        rw [← ENNReal.ofReal_pow (by positivity)]
        congr 1
        rw [Real.rpow_two]
        dsimp [A]
        ring
  exact lintegral_enorm_rpow_neg_lt_top_of_ball_le ha ha2 (by norm_num : (0 : ℝ) ≤ 1)
    hA (by simp [stdPlanarGaussian]) hball

/-- The inverse moment of a Brownian increment scales with the square root of its time lag. -/
theorem lintegral_planarBrownianMotion_increment_enorm_rpow_neg (x : ℂ) (s t : ℝ≥0) (a : ℝ) :
    (∫⁻ b, (ENNReal.ofReal ‖b t - b s‖) ^ (-a) ∂(planarBrownianMotion x)) =
      (ENNReal.ofReal (Real.sqrt (nndist (t : ℝ) (s : ℝ)))) ^ (-a) *
        ∫⁻ z, (ENNReal.ofReal ‖z‖) ^ (-a) ∂stdPlanarGaussian := by
  let f : ℂ → ℝ≥0∞ := fun z => (ENNReal.ofReal ‖z‖) ^ (-a)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hinc : Measurable (fun b : ContinuousPath ℂ => b t - b s) := by fun_prop
  rw [← lintegral_map hf hinc, planarBrownianMotion_map_increment,
    planarGaussian_eq_map_add_sqrt_mul, lintegral_map hf (by fun_prop)]
  dsimp [f]
  simp only [zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  exact lintegral_const_mul _ hf

/-- The inverse moment of a planar Brownian increment is the standard Gaussian moment
multiplied by the time lag to the power `-a/2`. -/
theorem lintegral_planarBrownianMotion_increment_enorm_rpow_neg_eq (x : ℂ) (s t : ℝ≥0) (a : ℝ) :
    (∫⁻ b, (ENNReal.ofReal ‖b t - b s‖) ^ (-a) ∂(planarBrownianMotion x)) =
      (ENNReal.ofReal (nndist (t : ℝ) (s : ℝ))) ^ (-a / 2) *
        ∫⁻ z, (ENNReal.ofReal ‖z‖) ^ (-a) ∂stdPlanarGaussian := by
  have hroot : ENNReal.ofReal (Real.sqrt (nndist (t : ℝ) (s : ℝ))) =
      (ENNReal.ofReal (nndist (t : ℝ) (s : ℝ))) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  rw [lintegral_planarBrownianMotion_increment_enorm_rpow_neg, hroot, ← ENNReal.rpow_mul]
  congr 2
  ring

end HarmonicBalls
