import HarmonicBalls.Steps.Sec11.PinchMetricMeasureObservable

/-! # Canonical metric-measure observables -/

namespace HarmonicBalls

open MeasureTheory

/-- A random Euclidean length metric with a simultaneous measurable
modification and an almost-everywhere measurable measure determine a common
measurable metric-measure observable. -/
theorem exists_canonicalMetricMeasureObservable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D D' : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hD' : ∀ x y, Measurable fun ω => D' ω x y)
    (hEq : ∀ᵐ ω ∂P, D' ω = D ω)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hμ : AEMeasurable μ P) :
    ∃ X : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d},
      AEMeasurable X P ∧ ∀ᵐ ω ∂P, (X ω).1 = μ ω ∧ (X ω).2.1 = D ω := by
  have hmetric' : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D' ω) := by
    filter_upwards [hEq, hmetric] with ω heq hm
    simpa only [heq] using hm
  obtain ⟨D'', hD'', hmetric'', heq'⟩ :=
    exists_measurable_lengthMetric_modification hD' hmetric'
  let dm : Ω → {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d} :=
    fun ω => ⟨D'' ω, hmetric'' ω⟩
  have hdm : Measurable dm := by
    apply Measurable.subtype_mk
    exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => hD'' x y
  refine ⟨fun ω => (μ ω, dm ω), hμ.prodMk hdm.aemeasurable, ?_⟩
  filter_upwards [hEq, heq'] with ω heq heq'
  exact ⟨rfl, heq'.trans heq⟩

/-- The staged singular-field metric axioms and the LQG measure construction
supply the canonical observable. The staged axioms remain explicit. -/
theorem exists_canonicalMetricMeasureObservable_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∃ X : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d},
      AEMeasurable X P ∧ ∀ᵐ ω ∂P, (X ω).1 = μ ω ∧ (X ω).2.1 = D ω := by
  obtain ⟨D', hD', heq⟩ :=
    exists_measurable_metric_modification_of_metricFieldAxioms haxioms hgff hγ hγ₂ hα hD
  exact exists_canonicalMetricMeasureObservable hD' heq
    (ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD) (hgff.aemeasurable_lqgMeasure hμ)

/-- The joint law does not depend on the almost-sure version chosen for the
canonical metric-measure observable. -/
theorem canonicalMetricMeasureObservable_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {X X' : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d}}
    (hX : ∀ᵐ ω ∂P, (X ω).1 = μ ω ∧ (X ω).2.1 = D ω)
    (hX' : ∀ᵐ ω ∂P, (X' ω).1 = μ ω ∧ (X' ω).2.1 = D ω) :
    P.map X = P.map X' := by
  apply Measure.map_congr
  filter_upwards [hX, hX'] with ω hω hω'
  apply Prod.ext
  · exact hω.1.trans hω'.1.symm
  · apply Subtype.ext
    exact hω.2.trans hω'.2.symm

#print axioms canonicalMetricMeasureObservable_map_eq
#print axioms exists_canonicalMetricMeasureObservable
#print axioms exists_canonicalMetricMeasureObservable_of_metricFieldAxioms

end HarmonicBalls
