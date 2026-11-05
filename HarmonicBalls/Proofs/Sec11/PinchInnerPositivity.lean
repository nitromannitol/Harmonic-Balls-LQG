import HarmonicBalls.Proofs.Sec11.PinchJointEventAE

/-! # Measurable positive subsets of pinch events -/

namespace HarmonicBalls

open MeasureTheory Filter Set

universe u

/-- Positive outer measure of the strengthened event gives a measurable positive
subset. The representative is jointly measurable in the center. -/
theorem exists_measurable_pos_subset_internal_pinch
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z}) :
    ∃ E ⊆ {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z},
      MeasurableSet E ∧ 0 < P E := by
  obtain ⟨F, hF, hFae⟩ :=
    exists_jointlyMeasurable_pinchPointEventWithInternalBounds P hconfig M hr hD hmetric hμ hloc
  have hmeas : MeasurableSet {ω | (ω, z) ∈ F} :=
    hF.preimage (measurable_id.prodMk measurable_const)
  have hnull : NullMeasurableSet
      {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z} P := by
    apply hmeas.nullMeasurableSet.congr
    filter_upwards [hFae] with ω hω
    exact propext (hω z)
  obtain ⟨E, hsub, hE, heq⟩ := hnull.exists_measurable_subset_ae_eq
  exact ⟨E, hsub, hE, (measure_congr heq).symm ▸ hpos⟩

/-- With the same hypotheses, one can choose a measurable positive subset of
the ordinary pinch event, on which the metric is a Euclidean length metric. -/
theorem exists_measurable_pos_subset_pinch
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z}) :
    ∃ E ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M r z ∧
      IsEuclideanLengthMetric (D ω)}, MeasurableSet E ∧ 0 < P E := by
  obtain ⟨E, hsub, hE, hEpos⟩ :=
    exists_measurable_pos_subset_internal_pinch P hconfig M z hr hD hmetric hμ hloc hpos
  have hnull : NullMeasurableSet {ω | IsEuclideanLengthMetric (D ω)} P := by
    apply (nullMeasurableSet_univ (μ := P)).congr
    filter_upwards [hmetric] with ω hω
    simp only [mem_univ, hω]
  obtain ⟨G, hGsub, hG, hGeq⟩ := hnull.exists_measurable_subset_ae_eq
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hGeq, hmetric] with ω heq hm
    exact heq.mpr hm
  have heq : E ∩ G =ᵐ[P] E := by
    filter_upwards [hGae] with ω hω
    simp [hω]
  refine ⟨E ∩ G, ?_, hE.inter hG, (measure_congr heq).symm ▸ hEpos⟩
  intro ω hω
  exact ⟨pinchPointEvent_of_internalBounds (hGsub hω.2) (hsub hω.1), hGsub hω.2⟩

/-- Conditional consumer for Lemma 11.12. The configuration is chosen before
all field parameters; the conditional input supplies regularity and strengthened
outer positivity for every frozen choice of parameters. -/
theorem pinchEventPositiveProbabilityStmt_of_internal_outer_positive
    (h : ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
      ∀ γ ξ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        IsLQGMetricOfField P γ ξ 0 hC D → ∀ M : ℝ, 0 < M →
        (∀ x y, Measurable fun ω => D ω x y) ∧
        (∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) ∧ AEMeasurable μ P ∧
        (∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) ∧
        0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M 1 0}) :
    PinchEventPositiveProbabilityStmt.{u} := by
  obtain ⟨U, T, Q', Q, hc, hdata⟩ := h
  refine ⟨U, T, Q', Q, hc, ?_⟩
  intro γ ξ hγ hγ' Ω _ P hC hcirc μ D hg hm hd M hM
  obtain ⟨hD, hmetric, hμ, hloc, hpos⟩ := hdata γ ξ hγ hγ' Ω P hC hcirc μ D hg hm hd M hM
  obtain ⟨E, hsub, hE, hEpos⟩ :=
    exists_measurable_pos_subset_pinch P hc M 0 (by norm_num : (0 : ℝ) < 1)
      hD hmetric hμ hloc hpos
  exact ⟨E, fun ω hω => (hsub hω).1, hE, hEpos⟩

#print axioms pinchEventPositiveProbabilityStmt_of_internal_outer_positive
#print axioms exists_measurable_pos_subset_internal_pinch
#print axioms exists_measurable_pos_subset_pinch

end HarmonicBalls
