import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstSmoothTransfer
import HarmonicBalls.Proofs.Sec11.CorrectedPinchPositiveOpenFirstShift

/-! Positive probability for the unshifted first pinch certificate. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- The first open-corridor certificate has positive probability. -/
theorem IsCorrectedPinchConfiguration.positive_wholePlane_open_first
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hP : 0 < P Set.univ)
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hconn : IsConnected (T \ thickening (3 * δ) W))
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1) :
    0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ} := by
  obtain ⟨g, hg, _, _, hp⟩ :=
    h.exists_positive_wholePlane_open_first_shift hξ P univ hP γ hC hcirc 𝔇 h𝔇 hgff hconn
  apply h.positive_open_first_of_wholePlane_smooth_shift P hC hcirc 𝔇 h𝔇 hgff ψ hψ hψint g hg
  simpa only [mem_univ, true_and, correctedOpenFirstCertificate] using hp

#print axioms IsCorrectedPinchConfiguration.positive_wholePlane_open_first
end HarmonicBalls
