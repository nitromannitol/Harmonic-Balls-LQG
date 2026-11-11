import HarmonicBalls.Steps.Sec11.PinchMetricMeasure
import HarmonicBalls.Proofs.Sec11.PinchInnerPositivity

/-! # Positive subsets from the staged metric-field axioms

The imported potential-theoretic infrastructure includes code by Leonardo Bonanno.
The metric-field axioms are staged literature inputs, not established here.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set

universe u

/-- The measurable subset lies inside the original strengthened event, even
when the given distance is only almost surely equal to a measurable version. -/
theorem exists_measurable_pos_subset_internal_pinch_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z}) :
    ∃ E ⊆ {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z},
      MeasurableSet E ∧ 0 < P E := by
  have hn := nullMeasurableSet_pinchPointEventWithInternalBounds_of_metricFieldAxioms
    hconfig M z hr haxioms hgff hγ hγ₂ hα hD hμ
  obtain ⟨E, hsub, hE, heq⟩ := hn.exists_measurable_subset_ae_eq
  exact ⟨E, hsub, hE, (measure_congr heq).symm ▸ hpos⟩

/-- The ordinary event and the length-metric property both hold pointwise on
this positive measurable subset of the original probability space. -/
theorem exists_measurable_pos_subset_pinch_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z}) :
    ∃ E ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M r z ∧
      IsEuclideanLengthMetric (D ω)}, MeasurableSet E ∧ 0 < P E := by
  obtain ⟨E, hsub, hE, hEpos⟩ :=
    exists_measurable_pos_subset_internal_pinch_of_metricFieldAxioms
      hconfig M z hr haxioms hgff hγ hγ₂ hα hD hμ hpos
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD
  have hn : NullMeasurableSet {ω | IsEuclideanLengthMetric (D ω)} P := by
    apply (nullMeasurableSet_univ (μ := P)).congr
    filter_upwards [hmetric] with ω hω
    simp only [mem_univ, hω]
  obtain ⟨G, hGsub, hG, hGeq⟩ := hn.exists_measurable_subset_ae_eq
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hGeq, hmetric] with ω heq hm
    exact heq.mpr hm
  have heq : E ∩ G =ᵐ[P] E := by
    filter_upwards [hGae] with ω hω
    simp [hω]
  refine ⟨E ∩ G, ?_, hE.inter hG, (measure_congr heq).symm ▸ hEpos⟩
  intro ω hω
  exact ⟨pinchPointEvent_of_internalBounds (hGsub hω.2) (hsub hω.1), hGsub hω.2⟩

/-- Conditional frozen 11.12 consumer: one configuration precedes all
parameter quantifiers. Outer positivity remains an explicit hypothesis. -/
theorem pinchEventPositiveProbabilityStmt_of_metricFieldAxioms_and_internal_outer_positive
    (h : ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
      ∀ γ ξ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        IsLQGMetricOfField P γ ξ 0 hC D → ∀ M : ℝ, 0 < M →
        LQGMetricFieldAxioms P γ ξ 0 hC hcirc ∧
        0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M 1 0}) :
    PinchEventPositiveProbabilityStmt.{u} := by
  obtain ⟨U, T, Q', Q, hc, hdata⟩ := h
  refine ⟨U, T, Q', Q, hc, ?_⟩
  intro γ ξ hγ hγ' Ω _ P hC hcirc μ D hg hm hd M hM
  obtain ⟨haxioms, hpos⟩ := hdata γ ξ hγ hγ' Ω P hC hcirc μ D hg hm hd M hM
  have hQ : 0 < lqgQ γ := by
    unfold lqgQ
    positivity
  obtain ⟨E, hsub, hE, hEpos⟩ :=
    exists_measurable_pos_subset_pinch_of_metricFieldAxioms hc M 0 (by norm_num : (0 : ℝ) < 1)
      haxioms hg hγ hγ' hQ hd hm hpos
  exact ⟨E, fun ω hω => (hsub hω).1, hE, hEpos⟩

#print axioms exists_measurable_pos_subset_internal_pinch_of_metricFieldAxioms
#print axioms exists_measurable_pos_subset_pinch_of_metricFieldAxioms
#print axioms pinchEventPositiveProbabilityStmt_of_metricFieldAxioms_and_internal_outer_positive

end HarmonicBalls
