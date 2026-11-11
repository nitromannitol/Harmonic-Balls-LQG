import HarmonicBalls.Proofs.GFF.CircleAverageLogRadiusFourthMoment

/-! # Absolute moments of log-radius circle-average increments

The exact Gaussian increment law gives all positive real absolute moments,
including across the normalized unit circle and at zero variance. The import
closure contains code by Leonardo Bonanno via LatticeProb.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Every positive real absolute moment of a real Gaussian is finite. -/
theorem integrable_gaussianReal_abs_rpow (m : ℝ) (v : ℝ≥0) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x : ℝ => |x| ^ p) (gaussianReal m v) := by
  have hm := (memLp_id_gaussianReal' (μ := m) (v := v) (ENNReal.ofReal p)
    ENNReal.ofReal_ne_top).integrable_norm_rpow'
  simpa [hp.le, Real.norm_eq_abs] using hm

/-- Every positive real absolute moment of a log-radius increment is finite. -/
theorem IsWholePlaneGFF.integrable_logRadius_circle_increment_abs_rpow
    (h : IsWholePlaneGFF P hC hcirc) (s t : ℝ) {p : ℝ} (hp : 0 < p) :
    Integrable (fun ω => |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0| ^ p) P := by
  have hlaw := h.logRadius_circle_increment_hasLaw s t
  have hi := integrable_gaussianReal_abs_rpow 0 (|s - t|).toNNReal hp
  rw [← hlaw.map_eq] at hi
  exact (integrable_map_measure
    ((Real.continuous_rpow_const hp.le).comp continuous_abs).aestronglyMeasurable
    hlaw.aemeasurable).1 hi

/-- A centered real Gaussian is obtained by scaling the standard normal by
its standard deviation, including when the variance is zero. -/
theorem gaussianReal_zero_eq_map_sqrt (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt v.coe_nonneg]

/-- Exact positive absolute moment scaling for a centered Gaussian. -/
theorem integral_gaussianReal_abs_rpow (v : ℝ≥0) {p : ℝ} (hp : 0 < p) :
    (∫ x : ℝ, |x| ^ p ∂gaussianReal 0 v) =
      (v : ℝ) ^ (p / 2) * ∫ x : ℝ, |x| ^ p ∂gaussianReal 0 1 := by
  rw [gaussianReal_zero_eq_map_sqrt v, integral_map (φ := fun x : ℝ => Real.sqrt v * x) (f := fun x : ℝ => |x| ^ p)
    (by fun_prop) ((Real.continuous_rpow_const hp.le).comp continuous_abs).aestronglyMeasurable]
  simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.mul_rpow (Real.sqrt_nonneg _) (abs_nonneg _), integral_const_mul]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul v.coe_nonneg]
  congr 1
  ring

/-- Exact positive absolute moment of every log-radius increment, with the
standard-normal absolute moment as the universal constant. -/
theorem IsWholePlaneGFF.integral_logRadius_circle_increment_abs_rpow
    (h : IsWholePlaneGFF P hC hcirc) (s t : ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ ω, |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0| ^ p ∂P) =
      |s - t| ^ (p / 2) * ∫ x : ℝ, |x| ^ p ∂gaussianReal 0 1 := by
  calc
    _ = ∫ x : ℝ, |x| ^ p ∂gaussianReal 0 (|s - t|).toNNReal := by
      simpa only [Function.comp_def] using
        (h.logRadius_circle_increment_hasLaw s t).integral_comp
          (f := fun x : ℝ => |x| ^ p)
          ((Real.continuous_rpow_const hp.le).comp continuous_abs).aestronglyMeasurable
    _ = _ := by
      rw [integral_gaussianReal_abs_rpow _ hp, Real.coe_toNNReal _ (abs_nonneg _)]

/-- Equal log radii have zero positive absolute moment. -/
theorem IsWholePlaneGFF.integral_logRadius_circle_increment_abs_rpow_self
    (h : IsWholePlaneGFF P hC hcirc) (s : ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ ω, |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp s) 0| ^ p ∂P) = 0 := by
  rw [h.integral_logRadius_circle_increment_abs_rpow s s hp]
  simp [Real.zero_rpow (show p / 2 ≠ 0 by positivity)]


end HarmonicBalls
