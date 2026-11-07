import HarmonicBalls.Proofs.Sec11.PinchWholePlaneSmoothTransfer
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstSecondGrowth

/-! # Conditional assembly of the whole-plane pinch event -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- The corrected pinch event has positive probability under LQG volume
    growth and the indicated outside-field and conditional-positivity inputs. -/
theorem IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ ξ γ α : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ A : Set ℂ, IsOpen A → A.Nonempty → 0 < μ ω A)
    (M : ℝ) (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
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
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
  let : MeasurableSpace Ω := m₀
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  exact h.positive_internal_pinch_of_open_first_second hξ P M hC hcirc 𝔇 μ h𝔇 hgff
    hμ hfull ψ hψ hψint
    (h.positive_wholePlane_first_second_of_growth hgrowth hξ hγ hγ₂ hα P hC hcirc
      𝔇 μ h𝔇 hgff hμ M m hm A hA hArep ha hb hinside)

#print axioms IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth
end HarmonicBalls
