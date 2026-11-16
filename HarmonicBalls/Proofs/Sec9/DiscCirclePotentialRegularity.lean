import HarmonicBalls.Proofs.Sec9.CorrectedSubharmonicUniqueness
import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Draft.Section4

/-!
# Continuity of circle-source disc potentials

A uniform circle source inside a disc has a continuous bounded Green potential on the closed disc.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace
open ComplexConjugate

/-- The continuous expression for the Green potential of a uniform circle source. -/
noncomputable def discCirclePotential (R : ℝ) (c : ℂ) (r : ℝ) (y : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * Real.log (max r ‖y - c‖) - greatestHarmonicMinorantBall R c y

/-- The disc harmonic correction is symmetric. -/
theorem greatestHarmonicMinorantBall_comm (R : ℝ) (x y : ℂ) :
    greatestHarmonicMinorantBall R x y = greatestHarmonicMinorantBall R y x := by
  unfold greatestHarmonicMinorantBall
  have h : ‖(R : ℂ) ^ 2 - conj x * y‖ = ‖(R : ℂ) ^ 2 - conj y * x‖ := by
    calc
      _ = ‖conj ((R : ℂ) ^ 2 - conj x * y)‖ := (Complex.norm_conj _).symm
      _ = _ := by simp [map_sub, map_mul, mul_comm]
  rw [h]

/-- The expression is continuous on the closed disc. -/
theorem continuousOn_discCirclePotential {R r : ℝ} {c : ℂ}
    (hr : 0 < r) (hsub : closedBall c r ⊆ ball 0 R) :
    ContinuousOn (discCirclePotential R c r) (closedBall 0 R) := by
  have hc : c ∈ ball (0 : ℂ) R := hsub (mem_closedBall_self hr.le)
  have hR : 0 < R := (norm_nonneg c).trans_lt (mem_ball_zero_iff.mp hc)
  intro y hy
  have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.mp hy
  have hpos : 0 < ‖(R : ℂ) ^ 2 - conj c * y‖ :=
    norm_sub_conj_mul_pos hR (mem_ball_zero_iff.mp hc) hyR
  unfold discCirclePotential greatestHarmonicMinorantBall
  have hmax : max r ‖y - c‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))
  fun_prop (disch := assumption)

/-- A measurable circle-integrable function is integrable against normalized angular measure. -/
theorem integrable_normalizedCircleMeasure_of_circleIntegrable {f : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hf : Measurable f) (hi : CircleIntegrable f c r) :
    Integrable f (Section6.normalizedCircleMeasure c r) := by
  unfold Section6.normalizedCircleMeasure
  apply (integrable_map_measure hf.aestronglyMeasurable
    (continuous_circleMap c r).measurable.aemeasurable).2
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  have hp := ((periodic_circleMap c r).comp f).intervalIntegrable (t := 0)
    (ne_of_gt Real.two_pi_pos) (by simpa only [CircleIntegrable, Function.comp_def, zero_add] using hi) (-Real.pi) Real.pi
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).mp hp

/-- The Green kernel is integrable against the circle source at every interior point. -/
theorem integrable_greenFunction_normalizedCircleMeasure {R r : ℝ} {c y : ℂ}
    (hr : 0 < r) (hsub : closedBall c r ⊆ ball 0 R) (hy : y ∈ ball (0 : ℂ) R) :
    Integrable (greenFunction (ball 0 R) y) (Section6.normalizedCircleMeasure c r) := by
  apply integrable_normalizedCircleMeasure_of_circleIntegrable
  · exact (measurable_greenFunction_ball_uncurry R).comp (measurable_const.prodMk measurable_id)
  · exact (circleAverage_greenFunction_ball_le hr hy hsub).1

/-- The Green kernel is integrable against the circle source at every point. -/
theorem integrable_greenFunction_normalizedCircleMeasure_all {R r : ℝ} {c y : ℂ}
    (hr : 0 < r) (hsub : closedBall c r ⊆ ball 0 R) :
    Integrable (greenFunction (ball 0 R) y) (Section6.normalizedCircleMeasure c r) := by
  by_cases hy : y ∈ ball (0 : ℂ) R
  · exact integrable_greenFunction_normalizedCircleMeasure hr hsub hy
  · have heq : greenFunction (ball 0 R) y = 0 := by
      ext w
      exact greenFunction_of_notMem_left hy w
    rw [heq]
    exact integrable_zero _ _ _

/-- Normalized angular measure has no atoms when the radius is positive. -/
theorem normalizedCircleMeasure_singleton {c z : ℂ} {r : ℝ} (hr : 0 < r) :
    Section6.normalizedCircleMeasure c r {z} = 0 := by
  unfold Section6.normalizedCircleMeasure
  rw [Measure.map_apply (continuous_circleMap c r).measurable (measurableSet_singleton z)]
  have hzero : volume (circleMap c r ⁻¹' {z}) = 0 :=
    ((countable_singleton z).preimage_circleMap c hr.ne').measure_zero volume
  have hrestrict : (volume.restrict (Ioc (-Real.pi) Real.pi)) (circleMap c r ⁻¹' {z}) = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.restrict_le_self (μ := volume)
      (s := Ioc (-Real.pi) Real.pi) _).trans hzero.le)
  rw [Measure.smul_apply, hrestrict, smul_zero]

/-- The negative circle potential is a test in the existing class. -/
theorem neg_greenPotential_normalizedCircleMeasure_mem_testClass
    {R r : ℝ} {c z : ℂ} {Λ : Set ℂ} (hr : 0 < r)
    (hsub : closedBall c r ⊆ ball 0 R) (hΛ : closure Λ ⊆ ball 0 R) :
    -greenPotential (ball 0 R) (Section6.normalizedCircleMeasure c r) ∈
      subharmonicBallTestClass Λ z := by
  refine ⟨ball 0 R, closedBall c r, 0, Section6.normalizedCircleMeasure c r, 0,
    isOpen_ball, hΛ, isCompact_closedBall _ _, hsub, inferInstance,
    (normalizedCircleMeasure_finite_and_supported c hr.le).1, ?_,
    (normalizedCircleMeasure_finite_and_supported c hr.le).2, ?_, ?_,
    normalizedCircleMeasure_singleton hr, integrable_greenFunction_normalizedCircleMeasure_all hr hsub, ?_⟩
  · simp
  · simp
  · exact harmonicOnNhd_const 0
  · ext x
    simp [greenPotential]

/-- In the open disc the expression is the potential of normalized circle measure. -/
theorem discCirclePotential_eq_integral {R r : ℝ} {c y : ℂ}
    (hr : 0 < r) (hsub : closedBall c r ⊆ ball 0 R) (hy : y ∈ ball (0 : ℂ) R) :
    discCirclePotential R c r y =
      ∫ w, greenFunction (ball 0 R) y w ∂(Section6.normalizedCircleMeasure c r) := by
  rw [integral_normalizedCircleMeasure_of_measurable c r]
  · rw [circleAverage_greenFunction_ball_eq_log_max hr hy hsub]
    simp only [discCirclePotential, greatestHarmonicMinorantBall_comm R c y]
  · exact (measurable_greenFunction_ball_uncurry R).comp (measurable_const.prodMk measurable_id)

/-- The extension vanishes on the boundary of the source disc. -/
theorem discCirclePotential_eq_zero_of_norm_eq {R r : ℝ} {c y : ℂ}
    (hr : 0 < r) (hsub : closedBall c r ⊆ ball 0 R) (hy : ‖y‖ = R) :
    discCirclePotential R c r y = 0 := by
  have hc : c ∈ ball (0 : ℂ) R := hsub (mem_closedBall_self hr.le)
  have hR : 0 < R := (norm_nonneg c).trans_lt (mem_ball_zero_iff.mp hc)
  have hyout : y ∉ closedBall c r := by
    intro h
    have := mem_ball_zero_iff.mp (hsub h)
    linarith
  have hdist : r < ‖y - c‖ := by
    have : ¬ dist y c ≤ r := by simpa [mem_closedBall] using hyout
    simpa [dist_eq_norm] using lt_of_not_ge this
  have hnorm : ‖(R : ℂ) ^ 2 - conj c * y‖ = R * ‖y - c‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hR.le (norm_nonneg _))).mp
    simpa only [hy, sub_self, mul_zero, add_zero, norm_sub_rev c y, mul_pow] using
      norm_sq_sub_conj_mul R c y
  unfold discCirclePotential greatestHarmonicMinorantBall
  rw [max_eq_right hdist.le, hnorm, Real.log_mul hR.ne' (ne_of_gt (lt_trans hr hdist))]
  ring

/-- On the boundary the extension agrees with the Green integral. -/
theorem discCirclePotential_eq_integral_of_norm_eq {R r : ℝ} {c y : ℂ}
    (hr : 0 < r) (hsub : closedBall c r ⊆ ball 0 R) (hy : ‖y‖ = R) :
    discCirclePotential R c r y =
      ∫ w, greenFunction (ball 0 R) y w ∂(Section6.normalizedCircleMeasure c r) := by
  rw [discCirclePotential_eq_zero_of_norm_eq hr hsub hy]
  simp only [greenFunction_ball_comm R y, greenFunction_ball_of_le_norm hy.ge, integral_zero]

/-- On the closed disc the continuous expression equals the Green potential. -/
theorem discCirclePotential_eq_integral_of_mem_closedBall {R r : ℝ} {c y : ℂ}
    (hr : 0 < r) (hsub : closedBall c r ⊆ ball 0 R) (hy : y ∈ closedBall (0 : ℂ) R) :
    discCirclePotential R c r y =
      ∫ w, greenFunction (ball 0 R) y w ∂(Section6.normalizedCircleMeasure c r) := by
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hy) with h | h
  · exact discCirclePotential_eq_integral hr hsub (mem_ball_zero_iff.mpr h)
  · exact discCirclePotential_eq_integral_of_norm_eq hr hsub h

/-- The circle-source potential has a bounded continuous extension to the closed disc. -/
theorem discCirclePotential_bounded {R r : ℝ} {c : ℂ}
    (hr : 0 < r) (hsub : closedBall c r ⊆ ball 0 R) :
    Bornology.IsBounded (Set.image (discCirclePotential R c r) (closedBall 0 R)) :=
  (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn
    (continuousOn_discCirclePotential hr hsub) |>.isBounded

end HarmonicBalls
