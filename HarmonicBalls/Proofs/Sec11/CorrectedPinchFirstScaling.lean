import HarmonicBalls.Steps.Sec11.PinchConstantScaling
import HarmonicBalls.Steps.Sec11.PinchLocalContraction

/-! Constant rescaling of the open-corridor certificate for the first pinch event. -/

namespace HarmonicBalls

open Set Metric MeasureTheory
open scoped ENNReal

/-- Positive rescaling preserves the two inequalities in the open-corridor
certificate. This holds without finiteness assumptions on internal distances. -/
theorem correctedPinch_open_first_const_mul
    (D : ℂ → ℂ → ℝ) (Q' Q W T : Set ℂ) (δ : ℝ) {c : ℝ} (hc : 0 < c) :
    ((⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (fun x y => c * D x y)
      (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
        closure (thickening (2 * δ) W))) 0 y) <
        ENNReal.ofReal (setDist (fun x y => c * D x y) Q' (frontier Q)) ∧
      internalDiam (fun x y => c * D x y) δ (T \ thickening (3 * δ) W) <
        ENNReal.ofReal (setDist (fun x y => c * D x y) {0} (sphere 0 δ))) ↔
    ((⨆ y ∈ sphere (0 : ℂ) 5, internalMetric D
      (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
        closure (thickening (2 * δ) W))) 0 y) <
        ENNReal.ofReal (setDist D Q' (frontier Q)) ∧
      internalDiam D δ (T \ thickening (3 * δ) W) <
        ENNReal.ofReal (setDist D {0} (sphere 0 δ))) := by
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hct : ENNReal.ofReal c ≠ ∞ := ENNReal.ofReal_ne_top
  simp only [internalDiam, internalMetric_const_mul D hc, setDist_const_mul D hc.le,
    ENNReal.ofReal_mul hc.le, ← ENNReal.mul_iSup,
    ENNReal.mul_lt_mul_iff_right hc0 hct]

#print axioms correctedPinch_open_first_const_mul

end HarmonicBalls
