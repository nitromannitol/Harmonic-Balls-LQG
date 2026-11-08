import HarmonicBalls.Proofs.GFF.CircleAverageRadialIncrements
import LatticeProb.Prob.BrownianMomentsCore

/-! # Fourth moments of log-radius circle-average increments

The joint Gaussian circle law and the concentric covariance give an exact
increment estimate on the whole real log-radius line. The Gaussian fourth
moment is from Leonardo Bonanno's formalization, via Lattice-Probability.
No choice of a continuous representative is made.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory NNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The log-radius increment has variance equal to the distance in log radius,
including increments crossing the normalized unit circle. -/
theorem IsWholePlaneGFF.variance_logRadius_circle_increment
    (h : IsWholePlaneGFF P hC hcirc) (s t : ℝ) :
    Var[fun ω => hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0; P] = |s - t| := by
  simpa only [Real.log_exp] using
    h.variance_circle_sub_circle (Real.exp_pos s) (Real.exp_pos t) 0

/-- The log-radius increment has the centered Gaussian law with variance
`|s - t|`, also when `s = t`. -/
theorem IsWholePlaneGFF.logRadius_circle_increment_hasLaw
    (h : IsWholePlaneGFF P hC hcirc) (s t : ℝ) :
    HasLaw (fun ω => hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0)
      (gaussianReal 0 (|s - t|).toNNReal) P := by
  have hg := h.hasGaussianLaw_circle_increment (Real.exp_pos s) (Real.exp_pos t)
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, h.integral_circle_increment (Real.exp_pos s) (Real.exp_pos t),
    h.variance_logRadius_circle_increment]

/-- The fourth power of every log-radius increment is integrable. -/
theorem IsWholePlaneGFF.integrable_logRadius_circle_increment_fourth
    (h : IsWholePlaneGFF P hC hcirc) (s t : ℝ) :
    Integrable (fun ω => (hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0) ^ 4) P := by
  have hlaw := h.logRadius_circle_increment_hasLaw s t
  have hi := LatticeProb.gaussianReal_integrable_fourth_power (|s - t|).toNNReal
  rw [← hlaw.map_eq] at hi
  exact (integrable_map_measure (by fun_prop) hlaw.aemeasurable).1 hi

/-- Exact fourth moment for all log radii. -/
theorem IsWholePlaneGFF.integral_logRadius_circle_increment_fourth
    (h : IsWholePlaneGFF P hC hcirc) (s t : ℝ) :
    (∫ ω, (hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0) ^ 4 ∂P) =
      3 * |s - t| ^ 2 := by
  calc
    _ = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 (|s - t|).toNNReal := by
      simpa only [Function.comp_def] using
        (h.logRadius_circle_increment_hasLaw s t).integral_comp (f := fun x : ℝ => x ^ 4)
          (by fun_prop)
    _ = _ := by rw [LatticeProb.gaussianReal_fourth_moment, Real.coe_toNNReal _ (abs_nonneg _)]

/-- At equal log radii the fourth moment is zero. -/
theorem IsWholePlaneGFF.integral_logRadius_circle_increment_fourth_self
    (h : IsWholePlaneGFF P hC hcirc) (s : ℝ) :
    (∫ ω, (hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp s) 0) ^ 4 ∂P) = 0 := by
  rw [h.integral_logRadius_circle_increment_fourth]
  simp

/-- A uniform fourth-moment increment estimate, valid over all real log radii. -/
theorem IsWholePlaneGFF.integral_logRadius_circle_increment_fourth_le
    (h : IsWholePlaneGFF P hC hcirc) (s t : ℝ) :
    (∫ ω, |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0| ^ 4 ∂P) ≤
      3 * |s - t| ^ 2 := by
  simpa only [(show Even 4 by decide).pow_abs] using
    (h.integral_logRadius_circle_increment_fourth s t).le

#print axioms IsWholePlaneGFF.variance_logRadius_circle_increment
#print axioms IsWholePlaneGFF.logRadius_circle_increment_hasLaw
#print axioms IsWholePlaneGFF.integrable_logRadius_circle_increment_fourth
#print axioms IsWholePlaneGFF.integral_logRadius_circle_increment_fourth
#print axioms IsWholePlaneGFF.integral_logRadius_circle_increment_fourth_self
#print axioms IsWholePlaneGFF.integral_logRadius_circle_increment_fourth_le

end HarmonicBalls
