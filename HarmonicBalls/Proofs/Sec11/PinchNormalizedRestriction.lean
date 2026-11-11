import HarmonicBalls.Steps.Sec11.PinchLocalData
import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent
import HarmonicBalls.Proofs.Sec8.LocalMeasureRatios

/-! # The pinch event under normalized local measure data -/

namespace HarmonicBalls
open MeasureTheory Metric Set
open scoped ENNReal

/-- Normalizing the restriction of the measure to any set containing the
pinch ball, and independently rescaling the metric, preserves the event. -/
theorem pinchPointEventWithInternalBounds_normalizedRestriction
    {μ : Measure ℂ} {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U T Q' Q B : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hB : ball z (6 * r) ⊆ B) (hzero : μ B ≠ 0) (htop : μ B ≠ ∞) :
    pinchPointEventWithInternalBounds (normalizedRestriction μ B)
      (fun x y => c * D x y) U T Q' Q M r z ↔
      pinchPointEventWithInternalBounds μ D U T Q' Q M r z := by
  have hlocal : (normalizedRestriction μ B).restrict (ball z (6 * r)) =
      ((μ B)⁻¹ • μ).restrict (ball z (6 * r)) := by
    rw [normalizedRestriction, Measure.restrict_smul,
      Measure.restrict_restrict_of_subset hB, Measure.restrict_smul]
  exact (pinchPointEventWithInternalBounds_iff_of_local_data (hD.const_mul hc)
    (hD.const_mul hc) hconfig M z hr (fun _ _ _ _ => rfl) hlocal).trans
      (pinchPointEventWithInternalBounds_const_mul μ D U T Q' Q M r z hc
        (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr hzero))

end HarmonicBalls
