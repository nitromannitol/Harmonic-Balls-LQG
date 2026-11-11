import HarmonicBalls.Proofs.Sec11.ConditionalPinchThresholdsNull
import HarmonicBalls.Steps.Sec11.PinchAuxiliaryThresholds

/-! # Conditional assembly of the second pinch event -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Outside measurability and conditional mass-diameter positivity for null-measurable events imply
that the second auxiliary event intersects any positive outside event. -/
theorem positive_pinchSecondEvent_of_conditional_null_massDiameter
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (U V : Set ℂ) {δ : ℝ} (hδ : 0 < δ) (M : ℝ)
    (hA : MeasurableSet[m] A) (hAp : 0 < P A)
    (ha : @Measurable Ω ℝ≥0∞ m _ (fun ω => ENNReal.ofReal
      (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)))))
    (hb : @Measurable Ω ℝ≥0∞ m _ (fun ω =>
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6))
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hgreen : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞)
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (D ω) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (D ω) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | ω ∈ A ∧ pinchSecondEvent (μ ω) (D ω) U V δ M} := by
  let : MeasurableSpace Ω := m₀
  have hfinite : ∀ᵐ ω ∂P,
      ENNReal.ofReal (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))) ≠ 0 ∧
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞ := by
    filter_upwards [hmetric, hgreen] with ω hD hG
    exact ⟨(ENNReal.ofReal_pos.mpr (hD.pinch_sphere_distances_pos hδ).1).ne',
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG⟩
  simpa only [pinchSecondEvent] using
    (positive_comparisons_of_conditional_null_thresholds P m hm A
      (fun ω => ENNReal.ofReal (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))))
      (fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)
      (fun ω => internalDiam (D ω) δ V) (fun ω => μ ω U)
      hA ha hb hAp hfinite hinside)

end HarmonicBalls
