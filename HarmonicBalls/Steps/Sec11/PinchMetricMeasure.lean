import HarmonicBalls.Steps.Sec11.CountableClearanceChains
import HarmonicBalls.Steps.Sec11.PinchRandomMeasure
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw
import HarmonicBalls.Steps.Sec11.MetricField

/-! # Pinch events for measurable random metrics and measures -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- A pointwise measurable random distance which is almost surely a Euclidean
length metric, together with a measurable random measure, determines a
null-measurable strengthened pinch event. -/
theorem nullMeasurableSet_pinchPointEventWithInternalBounds_of_measurable_metric_measure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hμ : Measurable μ) :
    NullMeasurableSet {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} P := by
  obtain ⟨D', hD', hmetric', hEq⟩ := exists_measurable_lengthMetric_modification hD hmetric
  have hdist : ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      Measurable fun ω => internalMetric (D' ω) (ball z (6 * r)) x y := by
    intro x hx y _
    exact measurable_internalMetric_of_lengthMetric isOpen_ball hx y hD' hmetric'
  have hm := nullMeasurableSet_pinchPointEventWithInternalBounds_of_measurable_measure
    (P := P) hconfig M z hr (Filter.Eventually.of_forall hmetric') hdist hμ
  apply hm.congr
  filter_upwards [hEq] with ω hω
  simp only [hω]

/-- Almost-everywhere measurability of the measure-valued map suffices. -/
theorem nullMeasurableSet_pinchPointEventWithInternalBounds_of_aeMeasurable_measure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hμ : AEMeasurable μ P) :
    NullMeasurableSet {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} P := by
  have hm := nullMeasurableSet_pinchPointEventWithInternalBounds_of_measurable_metric_measure
    hconfig M z hr hD hmetric hμ.measurable_mk
  apply hm.congr
  filter_upwards [hμ.ae_eq_mk] with ω hω
  simp only [hω]

/-- The metric may also be replaced by an almost-surely equal pointwise
measurable family. The same modification is used for every pair of points. -/
theorem nullMeasurableSet_pinchPointEventWithInternalBounds_of_metric_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D D' : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD' : ∀ x y, Measurable fun ω => D' ω x y)
    (hEq : ∀ᵐ ω ∂P, D' ω = D ω)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hμ : AEMeasurable μ P) :
    NullMeasurableSet {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} P := by
  have hmetric' : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D' ω) := by
    filter_upwards [hEq, hmetric] with ω heq hm
    simpa only [heq] using hm
  have hm := nullMeasurableSet_pinchPointEventWithInternalBounds_of_aeMeasurable_measure
    hconfig M z hr hD' hmetric' hμ
  apply hm.congr
  filter_upwards [hEq] with ω hω
  simp only [hω]

/-- The LQG measure supplies the required almost-everywhere measurability. -/
theorem nullMeasurableSet_pinchPointEventWithInternalBounds_of_lqgMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    NullMeasurableSet {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} P :=
  nullMeasurableSet_pinchPointEventWithInternalBounds_of_aeMeasurable_measure
    hconfig M z hr hD hmetric (h.aemeasurable_lqgMeasure hμ)

/-- The staged locality axiom gives one pointwise measurable modification of
the singular-field metric, simultaneously for all pairs of points. -/
theorem exists_measurable_metric_modification_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ}
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∃ D' : Ω → ℂ → ℂ → ℝ, (∀ x y, Measurable fun ω => D' ω x y) ∧
      ∀ᵐ ω ∂P, D' ω = D ω := by
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  obtain ⟨hmetric, hlocal, _, _⟩ := haxioms hgff hγ hγ₂ hα 𝔇 h𝔇
  obtain ⟨G, hG, hGeq⟩ := hlocal univ isOpen_univ
  refine ⟨fun ω x y => (G ω x y).toReal, ?_, ?_⟩
  · intro x y
    exact ((hG x y).mono (hgff.fieldSigmaAlgebra_le α₀ univ) le_rfl).ennreal_toReal
  · filter_upwards [hrepr, hmetric, hGeq] with ω hrepr hmetric hGeq
    funext x y
    have hnonneg := (hrepr x y).1
    have hbase : D ω = fun u v =>
        (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      rw [← (hrepr u v).2, ENNReal.toReal_ofReal (hrepr u v).1]
    have hlength : IsEuclideanLengthMetric (D ω) := by
      rw [hbase]
      exact hmetric.2
    have heq := hGeq x (mem_univ x) y (mem_univ y)
    rw [← hbase, ← hlength.ofReal_eq_internalMetric] at heq
    rw [← heq, ENNReal.toReal_ofReal hnonneg]

/-- The staged singular-field metric axioms and the LQG measure construction
imply null measurability of the strengthened pinch event. -/
theorem nullMeasurableSet_pinchPointEventWithInternalBounds_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    NullMeasurableSet {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} P := by
  obtain ⟨D', hD', heq⟩ :=
    exists_measurable_metric_modification_of_metricFieldAxioms haxioms hgff hγ hγ₂ hα hD
  exact nullMeasurableSet_pinchPointEventWithInternalBounds_of_metric_modification
    hconfig M z hr hD' heq
    (ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD) (hgff.aemeasurable_lqgMeasure hμ)

end HarmonicBalls
