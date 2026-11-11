import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstLawTransfer
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstScaling
import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent

/-! Transfer through normalized continuous metric observations. -/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- Positive random normalizations do not alter the first certificate, so
absolute continuity of normalized observations transfers its probability. -/
theorem IsCorrectedPinchConfiguration.positive_open_first_of_normalized_ac
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D₀ D₁ : Ω → ℂ → ℂ → ℝ) (F₀ F₁ : Ω → C(ℂ × ℂ, ℝ))
    (hF₀ : Measurable F₀) (hF₁ : Measurable F₁)
    (hD₀ : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D₀ ω))
    (hD₁ : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D₁ ω))
    (c₀ c₁ : Ω → ℝ)
    (hn₀ : ∀ᵐ ω ∂P, 0 < c₀ ω ∧ ∀ x y, F₀ ω (x, y) = c₀ ω * D₀ ω x y)
    (hn₁ : ∀ᵐ ω ∂P, 0 < c₁ ω ∧ ∀ x y, F₁ ω (x, y) = c₁ ω * D₁ ω x y)
    (hac : P.map F₁ ≪ P.map F₀)
    (hp : 0 < P {ω | correctedOpenFirstCertificate (D₁ ω) W T Q' Q δ}) :
    0 < P {ω | correctedOpenFirstCertificate (D₀ ω) W T Q' Q δ} := by
  have hl₀ : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => F₀ ω (x, y)) := by
    filter_upwards [hD₀, hn₀] with ω hd hn
    have he : (fun x y => F₀ ω (x, y)) = fun x y => c₀ ω * D₀ ω x y := by
      funext x y; exact hn.2 x y
    rw [he]
    exact hd.const_mul hn.1
  have hl₁ : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => F₁ ω (x, y)) := by
    filter_upwards [hD₁, hn₁] with ω hd hn
    have he : (fun x y => F₁ ω (x, y)) = fun x y => c₁ ω * D₁ ω x y := by
      funext x y; exact hn.2 x y
    rw [he]
    exact hd.const_mul hn.1
  have he₀ : {ω | correctedOpenFirstCertificate (fun x y => F₀ ω (x, y)) W T Q' Q δ} =ᵐ[P]
      {ω | correctedOpenFirstCertificate (D₀ ω) W T Q' Q δ} := by
    filter_upwards [hn₀] with ω hn
    apply propext
    simp_rw [hn.2]
    exact correctedPinch_open_first_const_mul (D₀ ω) Q' Q W T δ hn.1
  have he₁ : {ω | correctedOpenFirstCertificate (fun x y => F₁ ω (x, y)) W T Q' Q δ} =ᵐ[P]
      {ω | correctedOpenFirstCertificate (D₁ ω) W T Q' Q δ} := by
    filter_upwards [hn₁] with ω hn
    apply propext
    simp_rw [hn.2]
    exact correctedPinch_open_first_const_mul (D₁ ω) Q' Q W T δ hn.1
  rw [← measure_congr he₀]
  apply h.positive_open_first_of_ac P F₀ F₁ hF₀ hF₁ hl₀ hl₁ hac
  rw [measure_congr he₁]
  exact hp


end HarmonicBalls
