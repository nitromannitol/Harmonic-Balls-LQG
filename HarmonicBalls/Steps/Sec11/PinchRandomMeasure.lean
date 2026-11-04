import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable
import HarmonicBalls.Steps.Sec11.PinchMeasurable

/-! # Pinch events for measurable random measures -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- A measurable random measure supplies the potential and mass measurability
needed for the strengthened pinch event. -/
theorem nullMeasurableSet_pinchPointEventWithInternalBounds_of_measurable_measure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hdist : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      Measurable fun ω => internalMetric (D ω) (ball z (6 * r)) x y)
    (hμ : Measurable μ) :
    NullMeasurableSet {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} P := by
  apply nullMeasurableSet_pinchPointEventWithInternalBounds_of_ae hconfig M z hr hD hdist
  · exact (measurable_annulusGreenPotentialSup z (3 * r) (6 * r)).comp hμ
  · exact (Measure.measurable_coe
      (isOpen_rescaledSet hconfig.isOpen_U (ne_of_gt hr) z).measurableSet).comp hμ

end HarmonicBalls
