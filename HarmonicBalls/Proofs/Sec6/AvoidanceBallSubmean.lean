import HarmonicBalls.Proofs.Sec6.AvoidanceDiscRestart
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # Polar integration and compact avoidance -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric Complex
open scoped ENNReal

/-- Polar integration around an arbitrary centre, for a measurable nonnegative function. -/
theorem lintegral_translate_polar (c : ℂ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f (c + z)) =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * f (circleMap c r θ) := by
  rw [← Complex.lintegral_comp_polarCoord_symm (fun z => f (c + z))]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hfun : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * f (circleMap c p.1 p.2)) := by
    have h1 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1) := by fun_prop
    have h2 : Measurable (fun p : ℝ × ℝ => circleMap c p.1 p.2) := by
      unfold circleMap
      fun_prop
    exact h1.mul (hf.comp h2)
  have heq : (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
      f (c + Complex.polarCoord.symm p)) =
      fun p => ENNReal.ofReal p.1 * f (circleMap c p.1 p.2) := by
    funext p
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, smul_eq_mul]
  rw [heq, lintegral_prod _ hfun.aemeasurable]

/-- Integration on a disc in polar coordinates centred at its centre. -/
theorem lintegral_ball_polar (c : ℂ) (R : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in ball c R, f z) =
      ∫⁻ r in Ioo (0 : ℝ) R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * f (circleMap c r θ) := by
  let g := (ball c R).indicator f
  have hg : Measurable g := hf.indicator isOpen_ball.measurableSet
  calc
    (∫⁻ z in ball c R, f z) = ∫⁻ z, g z :=
      (lintegral_indicator isOpen_ball.measurableSet f).symm
    _ = ∫⁻ z, g (c + z) := ((measurePreserving_add_left volume c).lintegral_comp hg).symm
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * g (circleMap c r θ) := lintegral_translate_polar c hg
    _ = ∫⁻ r in Ioi (0 : ℝ), (Iio R).indicator (fun r =>
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal r * f (circleMap c r θ)) r := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hd (θ : ℝ) : dist (circleMap c r θ) c = r := by
        simpa only [abs_of_pos (show 0 < r from hr)] using
          (mem_sphere.mp (circleMap_mem_sphere' c r θ))
      by_cases hR : r < R
      · simp [hR, g, mem_ball, hd]
      · simp [hR, g, mem_ball, hd]
    _ = ∫⁻ r in Ioo (0 : ℝ) R, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * f (circleMap c r θ) := by
      rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      have hs : Iio R ∩ Ioi (0 : ℝ) = Ioo 0 R := by
        ext r
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
      rw [hs]

/-- Normalized circle integration in terms of angular Lebesgue measure. -/
theorem lintegral_normalizedCircleMeasure (c : ℂ) (r : ℝ)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂(normalizedCircleMeasure c r)) =
      ENNReal.ofReal ((2 * Real.pi)⁻¹) *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (circleMap c r θ) := by
  rw [normalizedCircleMeasure, lintegral_map hf (continuous_circleMap c r).measurable,
    lintegral_smul_measure]
  simp only [smul_eq_mul]
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)))]

/-- A circular submean bound on the outer half of a disc gives a ball bound. -/
theorem ball_submean_of_circle_submean (c : ℂ) {f : ℂ → ℝ≥0∞}
    (hf : Measurable f)
    (hcircle : ∀ r ∈ Ioo (1 / 8 : ℝ) (1 / 4),
      f c ≤ ∫⁻ z, f z ∂(normalizedCircleMeasure c r)) :
    let D : ℝ≥0∞ := ENNReal.ofReal (1 / 8) * ENNReal.ofReal (2 * Real.pi) *
      ENNReal.ofReal (1 / 8)
    D * f c ≤ ∫⁻ z in ball c (1 / 4 : ℝ), f z := by
  dsimp only
  let A : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi)
  have hA0 : A ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hAt : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv : ENNReal.ofReal ((2 * Real.pi)⁻¹) = A⁻¹ := by
    exact ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * Real.pi)
  have hθ : ∀ r ∈ Ioo (1 / 8 : ℝ) (1 / 4),
      A * f c ≤ ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (circleMap c r θ) := by
    intro r hr
    have h := hcircle r hr
    rw [lintegral_normalizedCircleMeasure c r hf, hinv] at h
    have hm : A * f c ≤ A * (A⁻¹ *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (circleMap c r θ)) := by gcongr
    rw [← mul_assoc, ENNReal.mul_inv_cancel hA0 hAt, one_mul] at hm
    exact hm
  have hbound : ∀ r ∈ Ioo (1 / 8 : ℝ) (1 / 4),
      ENNReal.ofReal (1 / 8) * A * f c ≤
        ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r * f (circleMap c r θ) := by
    intro r hr
    have hm : Measurable (fun θ : ℝ => f (circleMap c r θ)) :=
      hf.comp (continuous_circleMap c r).measurable
    rw [lintegral_const_mul _ hm]
    calc
      ENNReal.ofReal (1 / 8) * A * f c = ENNReal.ofReal (1 / 8) * (A * f c) := by rw [mul_assoc]
      _ ≤ ENNReal.ofReal (1 / 8) *
          ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (circleMap c r θ) := by gcongr; exact hθ r hr
      _ ≤ ENNReal.ofReal r *
          ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (circleMap c r θ) := by
        gcongr
        exact hr.1.le
  calc
    ENNReal.ofReal (1 / 8) * ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (1 / 8) * f c =
        ∫⁻ _ in Ioo (1 / 8 : ℝ) (1 / 4), ENNReal.ofReal (1 / 8) * A * f c := by
      rw [setLIntegral_const, Real.volume_Ioo]
      have he : (1 / 4 : ℝ) - 1 / 8 = 1 / 8 := by norm_num
      rw [he]
      dsimp only [A]
      ac_rfl
    _ ≤ ∫⁻ r in Ioo (1 / 8 : ℝ) (1 / 4), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * f (circleMap c r θ) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hbound r hr
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) (1 / 4), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * f (circleMap c r θ) := by
      apply lintegral_mono_set
      intro r hr
      exact ⟨by linarith [hr.1], hr.2⟩
    _ = ∫⁻ z in ball c (1 / 4 : ℝ), f z := (lintegral_ball_polar c _ hf).symm

/-- Uniform ball-submean estimate for unit-annulus compact avoidance. -/
theorem unit_goodAnnulus_avoidance_ball_submean :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧
      ∀ K : Set ℂ, IsCompact K → ∀ v ∈ sphere (0 : ℂ) (4 * 1),
        planarBrownianMotion v
          {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
            ContinuousPath.exitTime Kᶜ path} ≤
        C * ∫⁻ x in ball v (1 / 4 : ℝ), planarBrownianMotion x
          {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
            ContinuousPath.exitTime Kᶜ path} ∂volume := by
  let D : ℝ≥0∞ := ENNReal.ofReal (1 / 8) * ENNReal.ofReal (2 * Real.pi) *
      ENNReal.ofReal (1 / 8)
  have hD0 : D ≠ 0 := by
    dsimp only [D]
    positivity
  have hDt : D ≠ ∞ := by
    dsimp only [D]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  refine ⟨D⁻¹, ENNReal.inv_ne_zero.mpr hDt, ENNReal.inv_ne_top.mpr hD0, ?_⟩
  intro K hK v hv
  let f : ℂ → ℝ≥0∞ := fun x => planarBrownianMotion x
    {path | ContinuousPath.exitTime (annulus 0 3 5) path ≤ ContinuousPath.exitTime Kᶜ path}
  have hf : Measurable f := measurable_avoidance_probability
    (isOpen_ball.sdiff isClosed_closedBall) hK
  have hcircle : ∀ r ∈ Ioo (1 / 8 : ℝ) (1 / 4),
      f v ≤ ∫⁻ z, f z ∂(normalizedCircleMeasure v r) := by
    intro r hr
    apply unit_goodAnnulus_avoidance_le_circle_mean hK (by simpa using hv)
    · linarith [hr.1]
    · linarith [hr.2]
  have hsub := ball_submean_of_circle_submean v hf hcircle
  change D * f v ≤ ∫⁻ x in ball v (1 / 4 : ℝ), f x at hsub
  have hmul : D⁻¹ * (D * f v) ≤ D⁻¹ * ∫⁻ x in ball v (1 / 4 : ℝ), f x := by
    gcongr
  rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDt, one_mul] at hmul
  simpa [f] using hmul

end HarmonicBalls.Section6
