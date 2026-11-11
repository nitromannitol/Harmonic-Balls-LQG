import HarmonicBalls.Draft.Section11Corrected
import HarmonicBalls.Steps.Sec11.PinchAnnulusConnected

/-! # The buffered disk in the corrected pinch configuration -/

namespace HarmonicBalls
open Set Metric

/-- The removed neighborhood of `W` is an open disk whose closure lies in
`T`. This is the geometric premise for the planar disk-removal argument. -/
theorem IsCorrectedPinchConfiguration.exists_outer_removed_disk
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ thickening (3 * δ) W = ball c r ∧
      closure (ball c r) ⊆ T := by
  obtain ⟨c, ρU, ρV, ρW, hU, hV, hW⟩ := h.concentric
  have hδ := h.δ₀_mem.1
  have hVne : V.Nonempty := h.isConnected_U.nonempty.mono
    (subset_closure.trans h.closure_U_subset_V)
  have hWne : W.Nonempty := hVne.mono (subset_closure.trans h.closure_V_subset_W)
  have hρW : 0 < ρW := by rw [hW, nonempty_ball] at hWne; exact hWne
  refine ⟨c, ρW + 3 * δ, by positivity, ?_, ?_⟩
  · rw [hW, thickening_ball (by positivity : 0 < 3 * δ) hρW, add_comm]
  · have hsub : ball c (ρW + 3 * δ) ⊆ thickening (10 * δ) (closure W) := by
      have hball : ball c (ρW + 3 * δ) ⊆ thickening (10 * δ) W := by
        rw [hW, thickening_ball (by positivity : 0 < 10 * δ) hρW]
        exact ball_subset_ball (by linarith)
      exact hball.trans (thickening_subset_of_subset (10 * δ) subset_closure)
    exact (closure_mono hsub).trans (fun x hx => (h.buffer_W hx).1)

end HarmonicBalls
