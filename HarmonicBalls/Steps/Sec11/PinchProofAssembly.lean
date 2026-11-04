import HarmonicBalls.Steps.Sec11.PinchProofGeometry
import HarmonicBalls.Steps.Sec11.PinchAuxiliaryAssembly

/-! # Assembly of the local pinch event from the proof configuration

The proof configuration supplies the geometric containments and junctions.
The constrained-path inequality remains explicit.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- For a pinch proof configuration, the three auxiliary events and the
constrained-path inequality imply the strengthened pinch event. -/
theorem IsPinchPointProofConfiguration.pinchPointEventWithInternalBounds
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (μ : MeasureTheory.Measure ℂ) (M : ℝ)
    (hfirst : pinchFirstEvent D W T Q' Q δ)
    (hsecond : pinchSecondEvent μ D U V δ M)
    (hthird : pinchThirdEvent D V W δ)
    (hpaths : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q))) :
    pinchPointEventWithInternalBounds μ D U T Q' Q M 1 0 := by
  obtain ⟨hclA, hclB, hclC, hsubA, hsubB, hsubC⟩ := h.auxiliary_piece_containments
  exact pinchPointEventWithInternalBounds_of_auxiliary_events hD hnonneg μ U V W T Q' Q δ M
    hfirst hsecond hthird hpaths hclA hclB hclC hsubA hsubB hsubC
    h.outer_auxiliary_pieces_meet h.inner_auxiliary_pieces_meet h.δ₀_mem.1.le (by
      have hδ := h.δ₀_mem.2
      linarith)

end HarmonicBalls
