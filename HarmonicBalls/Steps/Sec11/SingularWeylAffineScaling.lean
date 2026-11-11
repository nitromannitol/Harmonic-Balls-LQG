import HarmonicBalls.Steps.Sec11.WeylMetricConstantScaling
import HarmonicBalls.Steps.Sec11.SingularWeylDilation
import HarmonicBalls.Steps.Sec11.InternalMetricPullback
import HarmonicBalls.Steps.Sec11.CurveConstantFiber

/-! # Dilation and constant rescaling of a singular Weyl metric -/

namespace HarmonicBalls

open Set MeasureTheory
open scoped ENNReal

/-- A dilation and positive constant rescaling of the base metric induce the
corresponding dilation and deterministic rescaling of its logarithmically
singular Weyl scaling. -/
theorem IsEuclideanLengthMetric.weylScaling_log_const_mul_comp_real_smul
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ α : ℝ)
    {k c : ℝ} (hk : 0 < k) (hc : 0 < c)
    (u v : ℂ) :
    weylScaling (fun x y => c * D (k • x) (k • y)) ξ
        (fun x => -α * Real.log ‖x‖) u v =
      (ENNReal.ofReal c * ENNReal.ofReal (Real.exp (ξ * (α * Real.log k)))) *
        weylScaling D ξ (fun x => -α * Real.log ‖x‖) (k • u) (k • v) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  have hpull : IsEuclideanLengthMetric (fun x y => D (k • x) (k • y)) :=
    hD.comp_homeomorph e
  rw [hpull.weylScaling_const_mul hc,
    weylScaling_log_comp_real_smul_of_base_zero_occupation D ξ α hk
      (fun _ _ hp => hD.ae_ne_of_lengthParametrized hp 0),
    mul_assoc]


end HarmonicBalls
