import HarmonicBalls.Proofs.Sec11.CorrectedPinchOutsideGreen
import HarmonicBalls.Proofs.Sec11.ConditionalPinchRepresentatives

/-! # Outside representative of the annular Green potential -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- An outside-measurable version of the restricted measure yields an
outside-measurable version of the Green-potential threshold. -/
theorem IsCorrectedPinchConfiguration.exists_green_outside_representative
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    (m : MeasurableSpace Ω) (μ ν : Ω → Measure ℂ) (M : ℝ)
    (hν : @Measurable Ω (Measure ℂ) m _ ν)
    (hνeq : ν =ᵐ[P] fun ω => (μ ω).restrict (closure W)ᶜ) :
    ∃ b : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ m _ b ∧
      b =ᵐ[P] fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 := by
  refine ⟨fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (ν ω) 0 3 6, ?_, ?_⟩
  · exact measurable_const.mul ((measurable_annulusGreenPotentialSup 0 3 6).comp hν)
  · filter_upwards [hνeq] with ω hω
    rw [hω, h.green_potential_restrict_outside]

/-- A version of the outside measure restriction supplies the Green
threshold required in conditional second-pinch assembly. -/
theorem IsCorrectedPinchConfiguration.positive_second_of_outside_measure_representative
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (μ ν : Ω → Measure ℂ) (hδ : 0 < δ) (M : ℝ)
    (a : Ω → ℝ≥0∞) (hA : MeasurableSet[m] A) (hAp : 0 < P A)
    (ha : @Measurable Ω ℝ≥0∞ m _ a)
    (hae : a =ᵐ[P] fun ω => ENNReal.ofReal
      (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))))
    (hν : @Measurable Ω (Measure ℂ) m _ ν)
    (hνeq : ν =ᵐ[P] fun ω => (μ ω).restrict (closure W)ᶜ)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hgreen : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞)
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (D ω) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (D ω) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | ω ∈ A ∧ pinchSecondEvent (μ ω) (D ω) U V δ M} := by
  obtain ⟨b, hb, hbe⟩ := h.exists_green_outside_representative P m μ ν M hν hνeq
  exact positive_pinchSecondEvent_of_conditional_null_massDiameter_representatives
    P m hm A D μ U V hδ M a b hA hAp ha hb hae hbe hmetric hgreen hinside

#print axioms IsCorrectedPinchConfiguration.exists_green_outside_representative
#print axioms IsCorrectedPinchConfiguration.positive_second_of_outside_measure_representative
end HarmonicBalls
