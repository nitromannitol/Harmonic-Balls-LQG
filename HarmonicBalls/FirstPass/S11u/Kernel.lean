import HarmonicBalls.Defs.GFF

/-!
# Kernel identities for the whole-plane covariance on circles

The whole-plane kernel `wholePlaneCov x y = log (max |x| 1 * max |y| 1 / |x - y|)` (Defs/GFF.lean) splits as
`a x + a y - log |x - y|` off the diagonal, with `a x = log max(|x|, 1)`. Averaging over a circle `∂B_ρ(z)` in the
variable `y` gives the Jensen formula (Duplantier-Sheffield, Section 3.1; Armitage-Gardiner for the logarithmic
potential). The diagonal `x = y` is handled by the codiscrete congruence of circle averages.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology

/-- `a x = log max(|x|, 1)`: the additive part of the whole-plane covariance kernel. -/
noncomputable def logMaxAbs (x : ℂ) : ℝ := Real.log (max ‖x‖ 1)

theorem logMaxAbs_continuous : Continuous logMaxAbs := by
  unfold logMaxAbs
  exact (continuous_norm.max continuous_const).log
    (fun x => ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _)))

/-- Off the diagonal the whole-plane kernel is `a x + a y - log |x - y|`. -/
theorem wholePlaneCov_eq_of_ne {x y : ℂ} (hxy : x ≠ y) :
    wholePlaneCov x y = logMaxAbs x + logMaxAbs y - Real.log ‖x - y‖ := by
  have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hy : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hd : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  unfold wholePlaneCov logMaxAbs
  rw [Real.log_div (mul_ne_zero hx hy) hd, Real.log_mul hx hy]

/-- Jensen's formula: the average of `log |y - w|` over `∂B_ρ(z)` is `log max(ρ, |z - w|)`. -/
theorem circleAverage_log_norm_sub_eq (z w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage (fun y => Real.log ‖y - w‖) z ρ = Real.log (max ρ ‖z - w‖) := by
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hρ.ne',
    Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul hρ.ne'
      (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))),
    mul_max_of_nonneg _ _ hρ.le, mul_one, mul_inv_cancel_left₀ hρ.ne']

/-- The circle average of the whole-plane kernel in `y` over `∂B_ρ(z)`, for every `x`. -/
theorem circleAverage_wholePlaneCov {z x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage (fun y => wholePlaneCov x y) z ρ =
      logMaxAbs x + Real.circleAverage logMaxAbs z ρ - Real.log (max ρ ‖x - z‖) := by
  have hcongr : (fun y => wholePlaneCov x y) =ᶠ[codiscreteWithin (sphere z |ρ|)]
      (fun y => logMaxAbs x + logMaxAbs y - Real.log ‖y - x‖) := by
    refine Filter.eventually_of_mem (compl_singleton_mem_codiscreteWithin x) ?_
    intro y hy
    have hyx : x ≠ y := fun h => hy (h.symm ▸ rfl)
    show wholePlaneCov x y = _
    rw [wholePlaneCov_eq_of_ne hyx, norm_sub_rev]
  rw [Real.circleAverage_congr_codiscreteWithin hcongr hρ.ne']
  have hc1 : CircleIntegrable (fun y => logMaxAbs x + logMaxAbs y) z ρ :=
    ContinuousOn.circleIntegrable' (continuous_const.add logMaxAbs_continuous).continuousOn
  have hc2 : CircleIntegrable (fun y => Real.log ‖y - x‖) z ρ :=
    circleIntegrable_log_norm_sub_const ρ
  rw [show (fun y => logMaxAbs x + logMaxAbs y - Real.log ‖y - x‖) =
      (fun y => logMaxAbs x + logMaxAbs y) - (fun y => Real.log ‖y - x‖) from rfl,
    Real.circleAverage_sub hc1 hc2, show (fun y => logMaxAbs x + logMaxAbs y) =
      (fun _ => logMaxAbs x) + logMaxAbs from rfl,
    Real.circleAverage_add (circleIntegrable_const _ _ _)
      (ContinuousOn.circleIntegrable' logMaxAbs_continuous.continuousOn),
    Real.circleAverage_const, circleAverage_log_norm_sub_eq z x hρ, norm_sub_rev]

end HarmonicBalls
