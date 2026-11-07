import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstSecond
import HarmonicBalls.Steps.Sec11.PinchGreenFinite

/-! # First and second pinch certificates under LQG volume growth -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Volume growth supplies the Green-potential finiteness needed to combine
the first and second certificates. The conditional positivity and outside
measurability hypotheses are still required. -/
theorem IsCorrectedPinchConfiguration.positive_wholePlane_first_second_of_growth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ ξ γ α₀ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (M : ℝ)
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (hA : MeasurableSet[m] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ})
    (ha : @Measurable Ω ℝ≥0∞ m _ (fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ)))))
    (hb : @Measurable Ω ℝ≥0∞ m _ (fun ω =>
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6))
    (hinside : ∀ n k : ℕ, 0 < n →
      @MeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  let : MeasurableSpace Ω := m₀
  exact h.positive_wholePlane_first_second hξ P hC hcirc 𝔇 μ h𝔇 hgff M m hm A hA
    hArep ha hb (ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth
      hgrowth hγ hγ₂ hα hgff hμ 3 (b := 6) (by norm_num)) hinside

#print axioms IsCorrectedPinchConfiguration.positive_wholePlane_first_second_of_growth
end HarmonicBalls
