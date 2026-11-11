import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.Proofs.Sec11.CorrectedPinchUniformFirstShift

/-!
# Section 11: the faithful buffered geometry in the corpus shift core

`IsBufferedPinchGeometry` (`FirstPass/S11h/Faithful.lean:43`; corrected paper lines 3157-3201, `[C42]`) implies the
corpus structure `IsPinchPointProofConfiguration` (`Draft/Section11.lean`) once `U` is nonempty. The deterministic
shift core `IsPinchPointProofConfiguration.exists_uniform_first_event_shift` then applies to the faithful geometry.

The hypothesis `U.Nonempty` is NOT part of `IsBufferedPinchGeometry`. The paper's `U` is an open disk. Without it the
conversion fails, and `PinchSecondEventFaithfulStmt` is false for `U = ∅`: `pinchSecondEvent` then requires
`ofReal M * _ < μ ∅ = 0`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- The faithful buffered keyhole geometry, with `U` nonempty, is a corpus pinch proof configuration (`[C42]`). -/
theorem IsBufferedPinchGeometry.toPinchPointProofConfiguration
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ) (hU : U.Nonempty) :
    IsPinchPointProofConfiguration U V W T Q' Q δ := by
  obtain ⟨c, ρU, ρV, ρW, hUc, hVc, hWc⟩ := h.concentric
  have hδ : 0 < 10 * δ := by linarith [h.delta_pos]
  have hUV : closure U ⊆ V := fun x hx => h.buffer_U (subset_closure (self_subset_thickening hδ _ hx))
  have hVW : closure V ⊆ W := fun x hx => h.buffer_V (subset_closure (self_subset_thickening hδ _ hx))
  have hVW' : V ⊆ W := fun x hx => hVW (subset_closure hx)
  have hUT : closure U ⊆ T := fun x hx => h.closure_W_subset_T (subset_closure (hVW' (hUV hx)))
  have hconn : IsConnected U := by
    rw [hUc] at hU ⊢
    exact (convex_ball c ρU).isConnected hU
  have hsph : sphere (0 : ℂ) 5 ⊆ frontier T := by
    intro x hx
    rw [frontier, mem_sdiff]
    refine ⟨h.sphere_subset_closure_T hx, fun hint => ?_⟩
    have h1 := (h.T_subset (interior_subset hint)).1
    rw [mem_sphere] at hx
    rw [mem_ball] at h1
    linarith
  have hbT : closure (thickening (10 * δ) T) ⊆ annulus 0 1 6 := by
    simpa only [thickening_closure] using h.buffer_T
  have hbU : closure (thickening (10 * δ) U) ⊆ V := by
    simpa only [thickening_closure] using h.buffer_U
  have hbV : closure (thickening (10 * δ) V) ⊆ W := by
    simpa only [thickening_closure] using h.buffer_V
  have hbW : closure (thickening (10 * δ) W) ⊆ annulus 0 1 2 := by
    have := h.buffer_W
    simp only [thickening_closure] at this
    exact fun x hx => (this hx).2
  have hbQ' : closure (thickening (10 * δ) Q') ⊆ Q := by
    simpa only [thickening_closure] using h.buffer_Q'
  have hbQ : closure (thickening (10 * δ) Q) ⊆ annulus 0 4 5 \ thickening (10 * δ) T := by
    simpa only [thickening_closure] using h.buffer_Q
  exact
    { toIsPinchPointConfiguration :=
        { isOpen_U := h.isOpen_U
          isConnected_U := hconn
          isOpen_T := h.isOpen_T
          isConnected_T := h.isConnected_T
          isOpen_Q' := h.isOpen_Q'
          isConnected_Q' := h.isConnected_Q'
          isOpen_Q := h.isOpen_Q
          isConnected_Q := h.isConnected_Q
          closure_U_subset := hUT
          closure_Q'_subset := h.closure_Q'_subset_Q
          exists_eq_ball := ⟨c, ρU, hUc⟩
          U_subset := h.U_subset
          Q_subset := fun x hx => h.closure_Q_subset (subset_closure hx)
          T_subset := h.T_subset
          sphere_subset_frontier := hsph }
      concentric := ⟨c, ρU, ρV, ρW, hUc, hVc, hWc⟩
      closure_U_subset_V := hUV
      closure_V_subset_W := hVW
      closure_W_subset_T := h.closure_W_subset_T
      V_subset := h.V_subset
      W_subset := h.W_subset
      δ₀_mem := ⟨h.delta_pos, by linarith [h.delta_lt]⟩
      thickening_T := hbT
      thickening_U := hbU
      thickening_V := hbV
      thickening_W := hbW
      thickening_Q' := hbQ'
      thickening_Q := hbQ }

#print axioms IsBufferedPinchGeometry.toPinchPointProofConfiguration

end HarmonicBalls
