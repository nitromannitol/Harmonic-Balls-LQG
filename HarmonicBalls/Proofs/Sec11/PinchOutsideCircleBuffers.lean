import HarmonicBalls.Proofs.Sec11.PinchGreenAnnularLocality

/-! # Outside buffers for the pinning and Green-annulus circles -/

namespace HarmonicBalls
open Set Metric

/-- The pinning circle and a reference circle in the Green annulus are both
contained in the open complement of the closed pinch core. -/
theorem IsCorrectedPinchConfiguration.pinning_reference_circles_subset_outside
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    sphere (0 : ℂ) 1 ∪ sphere 0 4 ⊆ (closure W)ᶜ := by
  have hW : closure W ⊆ annulus 0 1 2 := by
    have ht : closure W ⊆ thickening (10 * δ) (closure W) :=
      self_subset_thickening (by have := h.δ₀_mem.1; positivity) _
    exact ht.trans (subset_closure.trans (h.buffer_W.trans inter_subset_right))
  intro x hx hxW
  have hxW' := hW hxW
  rcases hx with hx | hx
  · have hx1 : dist x (0 : ℂ) = 1 := mem_sphere.mp hx
    have hx' : x ∈ closedBall (0 : ℂ) 1 := by rw [mem_closedBall]; linarith
    exact hxW'.2 hx'
  · have hx4 : dist x (0 : ℂ) = 4 := mem_sphere.mp hx
    have hx2 : dist x (0 : ℂ) < 2 := hxW'.1
    linarith

/-- A common positive collar of both circles remains outside the pinch core.
This gives the geometric buffer needed for local smooth circle approximations. -/
theorem IsCorrectedPinchConfiguration.exists_outside_pinning_reference_collar
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    ∃ ε : ℝ, 0 < ε ∧
      cthickening ε (sphere (0 : ℂ) 1 ∪ sphere 0 4) ⊆ (closure W)ᶜ := by
  exact ((isCompact_sphere (0 : ℂ) 1).union (isCompact_sphere 0 4)).exists_cthickening_subset_open
    isClosed_closure.isOpen_compl h.pinning_reference_circles_subset_outside

end HarmonicBalls
