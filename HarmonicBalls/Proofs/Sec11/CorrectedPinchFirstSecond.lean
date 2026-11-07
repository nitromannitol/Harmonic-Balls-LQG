import HarmonicBalls.Proofs.Sec11.CorrectedPinchPositiveOpenFirst
import HarmonicBalls.Proofs.Sec11.PinchSecondConditionalAssembly

/-! # Joint positivity of the first and second pinch certificates -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Conditional mass-diameter positivity and outside-field measurability
combine the first open-corridor certificate with the second auxiliary event. -/
theorem IsCorrectedPinchConfiguration.positive_wholePlane_first_second
    {U V W T Q' Q : Set ℂ} {δ ξ γ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hconn : IsConnected (T \ thickening (3 * δ) W)) (M : ℝ)
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (hA : MeasurableSet[m] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ})
    (ha : @Measurable Ω ℝ≥0∞ m _ (fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ)))))
    (hb : @Measurable Ω ℝ≥0∞ m _ (fun ω =>
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6))
    (hgreen : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞)
    (hinside : ∀ n k : ℕ, 0 < n →
      @MeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  let : MeasurableSpace Ω := m₀
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  have hp := h.positive_wholePlane_open_first hξ P (by simp) γ hC hcirc 𝔇 h𝔇
    hgff hconn ψ hψ hψint
  have hAp : 0 < P A := by rw [measure_congr hArep]; exact hp
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    filter_upwards [ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (by intro ω; fun_prop) (by intro x; fun_prop)] with ω hω
    exact hω.1
  have hpos := positive_pinchSecondEvent_of_conditional_massDiameter P m hm A
    (fun ω => 𝔇 (hC ω)) μ U V h.δ₀_mem.1 M hA hAp ha hb hmetric hgreen hinside
  have heq : {ω | ω ∈ A ∧ pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} =ᵐ[P]
      {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
        pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
    filter_upwards [hArep] with ω hω
    rw [hω]
  rwa [measure_congr heq] at hpos

#print axioms IsCorrectedPinchConfiguration.positive_wholePlane_first_second
end HarmonicBalls
