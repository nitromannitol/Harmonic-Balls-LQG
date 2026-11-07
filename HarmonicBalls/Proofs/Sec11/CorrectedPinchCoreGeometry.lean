import HarmonicBalls.Proofs.Sec11.ConditionalCoreMeasurability
import HarmonicBalls.Draft.Section11Corrected

/-! # Compact connected core for the corrected pinch configuration -/

namespace HarmonicBalls
open Set Metric

/-- The intermediate ball has compact connected closure; every set inside
the innermost ball is contained in the interior of that closure. -/
theorem IsCorrectedPinchConfiguration.closure_V_core
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    IsCompact (closure V) ∧ IsConnected (closure V) ∧ U ⊆ interior (closure V) := by
  have hUV : U ⊆ V := subset_closure.trans h.closure_U_subset_V
  obtain ⟨c, rU, rV, rW, hU, hV, hW⟩ := h.concentric
  have hVne : V.Nonempty := h.isConnected_U.nonempty.mono hUV
  have hrV : 0 < rV := by rw [hV, nonempty_ball] at hVne; exact hVne
  have hcV : IsConnected V := by rw [hV]; exact isConnected_ball hrV
  have hVopen : IsOpen V := by rw [hV]; exact isOpen_ball
  have hVbounded : Bornology.IsBounded V := by rw [hV]; exact isBounded_ball
  exact ⟨hVbounded.isCompact_closure, hcV.closure,
    hUV.trans (hVopen.subset_interior_iff.mpr subset_closure)⟩

#print axioms IsCorrectedPinchConfiguration.closure_V_core
end HarmonicBalls
