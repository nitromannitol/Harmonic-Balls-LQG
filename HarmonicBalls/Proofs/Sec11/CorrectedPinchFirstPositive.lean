import HarmonicBalls.Proofs.Sec11.PlanarDiskRemoval
import HarmonicBalls.Proofs.Sec11.CorrectedPinchPositiveOpenFirst

/-! # Positive first pinch certificate in corrected geometry -/

namespace HarmonicBalls
open MeasureTheory Metric Set
open scoped ENNReal

/-- The open first certificate has positive probability for every corrected
pinch configuration and every positive metric Weyl exponent. -/
theorem IsCorrectedPinchConfiguration.positive_open_first
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc) :
    0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ} := by
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  exact h.positive_wholePlane_open_first hξ P (by simp) γ hC hcirc 𝔇 h𝔇 hgff
    h.outer_piece_isConnected ψ hψ hψint

/-- The first auxiliary pinch event has positive probability in the same
setting. -/
theorem IsCorrectedPinchConfiguration.positive_first
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc) :
    0 < P {ω | pinchFirstEvent (𝔇 (hC ω)) W T Q' Q δ} :=
  h.positive_wholePlane_first hξ P γ hC hcirc 𝔇 h𝔇 hgff h.outer_piece_isConnected

end HarmonicBalls
