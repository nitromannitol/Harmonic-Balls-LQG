import HarmonicBalls.Proofs.Sec11.CorrectedPinchOpenFirstAssembly
import HarmonicBalls.Proofs.Sec11.WholePlaneInternalPinchWeyl

/-! # Third Weyl shift from the open first certificate -/

namespace HarmonicBalls
open MeasureTheory Metric Set
open scoped ENNReal

/-- The open-corridor certificate implies the first auxiliary event. -/
theorem correctedOpenFirstCertificate.first_event
    {D : ℂ → ℂ → ℝ} {W T Q' Q : Set ℂ} {δ : ℝ}
    (h : correctedOpenFirstCertificate D W T Q' Q δ) :
    pinchFirstEvent D W T Q' Q δ := by
  refine ⟨?_, h.2⟩
  apply lt_of_le_of_lt ?_ h.constrained_paths
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  exact le_iSup_of_le y (le_iSup_of_le hy (internalMetric_anti D inter_subset_left 0 y))

/-- A positive joint event for the open first certificate and the second
auxiliary event yields the strengthened pinch event after a smooth shift.
The conclusion retains the weighted measure and shifted field explicitly. -/
theorem IsCorrectedPinchConfiguration.exists_positive_open_first_internal_pinch_shift
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hA : 0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M}) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      0 < P {ω | pinchPointEventWithInternalBounds
        ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
        (𝔇 (addFunPairing (hC ω) f)) U T Q' Q M 1 0} := by
  apply h.toIsPinchPointProofConfiguration.exists_positive_measure_wholePlane_internal_pinch_shift
    hξ P γ M hC hcirc 𝔇 μ h𝔇 hgff
  apply hA.trans_le
  apply measure_mono
  intro ω hω
  exact ⟨hω.1.first_event, hω.2, hω.1.constrained_paths⟩

#print axioms correctedOpenFirstCertificate.first_event
#print axioms IsCorrectedPinchConfiguration.exists_positive_open_first_internal_pinch_shift
end HarmonicBalls
