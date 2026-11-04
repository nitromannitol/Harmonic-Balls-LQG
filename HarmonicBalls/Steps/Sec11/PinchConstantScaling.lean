import HarmonicBalls.Steps.Sec11.MetricConstantScaling
import HarmonicBalls.Steps.Sec11.InternalPinchScales
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureScaling

/-! # Constant rescaling of the local pinch event -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- The local pinch event is unchanged by independently rescaling the metric
and the measure by positive finite constants. -/
theorem pinchPointEventWithInternalBounds_const_mul
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ)
    {c : ℝ} (hc : 0 < c) {a : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞) :
    pinchPointEventWithInternalBounds (a • μ) (fun x y => c * D x y) U T Q' Q M r z ↔
      pinchPointEventWithInternalBounds μ D U T Q' Q M r z := by
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hct : ENNReal.ofReal c ≠ ∞ := ENNReal.ofReal_ne_top
  unfold pinchPointEventWithInternalBounds
  simp only [internalMetric_const_mul D hc, setDist_const_mul D hc.le,
    ENNReal.ofReal_mul hc.le, ← ENNReal.mul_iSup,
    annulusGreenPotentialSup_smul, Measure.smul_apply, smul_eq_mul,
    mul_left_comm (ENNReal.ofReal M) a, ENNReal.mul_lt_mul_iff_right hc0 hct,
    ENNReal.mul_lt_mul_iff_right ha hat]

end HarmonicBalls
