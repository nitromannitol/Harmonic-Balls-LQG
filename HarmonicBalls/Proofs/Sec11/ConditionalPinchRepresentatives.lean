import HarmonicBalls.Proofs.Sec11.PinchSecondConditionalAssemblyNull

/-! # Conditional threshold assembly with outside representatives -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Almost-surely equal outside-measurable representatives suffice for the
two thresholds; no pointwise measurability of the original observables is
needed. -/
theorem positive_comparisons_of_conditional_null_thresholds_representatives
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (a b x y a' b' : Ω → ℝ≥0∞)
    (hA : MeasurableSet[m] A) (ha' : @Measurable Ω ℝ≥0∞ m _ a')
    (hb' : @Measurable Ω ℝ≥0∞ m _ b') (hae : a' =ᵐ[P] a) (hbe : b' =ᵐ[P] b)
    (hAp : 0 < P A) (hfinite : ∀ᵐ ω ∂P, a ω ≠ 0 ∧ b ω ≠ ∞)
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | x ω < (n : ℝ≥0∞)⁻¹ ∧ (k : ℝ≥0∞) < y ω} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | x ω < (n : ℝ≥0∞)⁻¹ ∧ (k : ℝ≥0∞) < y ω}).indicator
        (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | ω ∈ A ∧ x ω < a ω ∧ b ω < y ω} := by
  let : MeasurableSpace Ω := m₀
  have hfinite' : ∀ᵐ ω ∂P, a' ω ≠ 0 ∧ b' ω ≠ ∞ := by
    filter_upwards [hae, hbe, hfinite] with ω ha hb hf
    simpa only [ha, hb] using hf
  have hp := positive_comparisons_of_conditional_null_thresholds P m hm A a' b' x y
    hA ha' hb' hAp hfinite' hinside
  have heq : {ω | ω ∈ A ∧ x ω < a' ω ∧ b' ω < y ω} =ᵐ[P]
      {ω | ω ∈ A ∧ x ω < a ω ∧ b ω < y ω} := by
    filter_upwards [hae, hbe] with ω ha hb
    simp only [ha, hb]
  rwa [measure_congr heq] at hp

/-- Conditional assembly of the second pinch event using outside-measurable
representatives of the metric separation and Green-potential thresholds. -/
theorem positive_pinchSecondEvent_of_conditional_null_massDiameter_representatives
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (U V : Set ℂ) {δ : ℝ} (hδ : 0 < δ) (M : ℝ) (a' b' : Ω → ℝ≥0∞)
    (hA : MeasurableSet[m] A) (hAp : 0 < P A)
    (ha' : @Measurable Ω ℝ≥0∞ m _ a') (hb' : @Measurable Ω ℝ≥0∞ m _ b')
    (hae : a' =ᵐ[P] fun ω => ENNReal.ofReal
      (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))))
    (hbe : b' =ᵐ[P] fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)
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
    (positive_comparisons_of_conditional_null_thresholds_representatives P m hm A
      (fun ω => ENNReal.ofReal (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))))
      (fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)
      (fun ω => internalDiam (D ω) δ V) (fun ω => μ ω U) a' b'
      hA ha' hb' hae hbe hAp hfinite hinside)

end HarmonicBalls
