import HarmonicBalls.Steps.Sec11.PinchMetricMeasure

/-! # Pinch events on the metric-measure observable space -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- The strengthened pinch event is measurable on pairs consisting of a
measure and a Euclidean length metric. The metric coordinate has the
pointwise evaluation sigma algebra restricted to the length metrics. -/
theorem measurableSet_pinchPointEventWithInternalBounds_on_lengthMetrics
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    MeasurableSet {p : Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d} |
      pinchPointEventWithInternalBounds p.1 p.2.1 U T Q' Q M r z} := by
  let Z := Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d}
  let D : Z → ℂ → ℂ → ℝ := fun p => p.2.1
  let μ : Z → Measure ℂ := fun p => p.1
  have hD : ∀ x y, Measurable fun p : Z => D p x y := by
    intro x y
    exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp
      (measurable_subtype_coe.comp measurable_snd))
  have hm : ∀ p : Z, IsEuclideanLengthMetric (D p) := fun p => p.2.2
  have hnonneg : ∀ p x y, 0 ≤ D p x y := by
    intro p x y
    have ht := (hm p).triangle x y x
    rw [(hm p).self_eq_zero, (hm p).symm y x] at ht
    linarith
  have hdist : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      Measurable fun p : Z => internalMetric (D p) (ball z (6 * r)) x y := by
    intro x hx y _
    exact measurable_internalMetric_of_lengthMetric isOpen_ball hx y hD hm
  have hgreen : Measurable fun p : Z => annulusGreenPotentialSup (μ p) z (3 * r) (6 * r) :=
    (measurable_annulusGreenPotentialSup z (3 * r) (6 * r)).comp measurable_fst
  have hmass : Measurable fun p : Z => μ p (rescaledSet U r z) :=
    (Measure.measurable_coe (isOpen_rescaledSet hconfig.isOpen_U (ne_of_gt hr) z).measurableSet).comp
      measurable_fst
  exact measurableSet_pinchPointEventWithInternalBounds hconfig M z hr hm hnonneg hdist hgreen hmass


end HarmonicBalls
