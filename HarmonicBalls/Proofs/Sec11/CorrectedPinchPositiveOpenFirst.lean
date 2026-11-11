import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstSmoothTransfer
import HarmonicBalls.Proofs.Sec11.CorrectedPinchPositiveOpenFirstShift
import HarmonicBalls.Steps.Sec11.CenteredFieldSigma

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

/-- The first pinch event has positive probability under the whole-plane
GFF law, provided the buffered outer piece is connected. -/
theorem IsCorrectedPinchConfiguration.positive_wholePlane_first
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hconn : IsConnected (T \ thickening (3 * δ) W)) :
    0 < P {ω | pinchFirstEvent (𝔇 (hC ω)) W T Q' Q δ} := by
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  have hp := h.positive_wholePlane_open_first hξ P (by simp) γ hC hcirc 𝔇 h𝔇
    hgff hconn ψ hψ hψint
  refine hp.trans_le (measure_mono ?_)
  intro ω hω
  change correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ at hω
  change pinchFirstEvent (𝔇 (hC ω)) W T Q' Q δ
  refine ⟨?_, hω.2⟩
  apply lt_of_le_of_lt ?_ hω.1
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply le_iSup_of_le y
  apply le_iSup_of_le hy
  apply internalMetric_anti
  intro x hx
  rw [thickening_union]
  intro hmem
  exact hx.2 (hmem.elim (fun hq => Or.inl (subset_closure hq))
    (fun hw => Or.inr (subset_closure hw)))

end HarmonicBalls
