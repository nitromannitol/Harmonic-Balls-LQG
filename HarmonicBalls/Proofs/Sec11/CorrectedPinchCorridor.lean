import HarmonicBalls.Draft.Section11Corrected
import HarmonicBalls.Steps.Sec11.PinchConstrainedFiniteness

/-! # The corrected obstacle-free pinch corridor -/

namespace HarmonicBalls

open Metric Set
open scoped ENNReal

/-- The buffered obstacles stay strictly inside the radius-five ball. In
particular the entire exterior of that ball is available to a corridor. -/
theorem IsPinchPointProofConfiguration.obstacle_closures_subset_ball_five
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) :
    closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W) ⊆
      ball (0 : ℂ) 5 := by
  have hδ : 0 < δ := h.δ₀_mem.1
  apply union_subset
  · exact (closure_mono (thickening_mono (by linarith : 2 * δ ≤ 10 * δ) Q)).trans
      (h.thickening_Q.trans (fun _ hx => hx.1.1))
  · exact (closure_mono (thickening_mono (by linarith : 2 * δ ≤ 10 * δ) W)).trans
      (h.thickening_W.trans (fun _ hx => (ball_subset_ball (by norm_num : (2 : ℝ) ≤ 5)) hx.1))

/-- The radius-five sphere is obstacle-free even after taking closures. -/
theorem IsPinchPointProofConfiguration.sphere_five_avoids_obstacle_closures
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) :
    sphere (0 : ℂ) 5 ⊆
      (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))ᶜ := by
  intro x hx hobs
  have hin := h.obstacle_closures_subset_ball_five hobs
  rw [mem_ball] at hin
  rw [mem_sphere] at hx
  linarith

/-- The corrected corridor is open, and is connected whenever it contains
the origin. -/
theorem pinchCorridor_open_connected {W Q : Set ℂ} {δ : ℝ}
    (hzero : (0 : ℂ) ∈ pinchCorridor W Q δ) :
    IsOpen (pinchCorridor W Q δ) ∧ IsConnected (pinchCorridor W Q δ) := by
  constructor
  · exact (isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)).connectedComponentIn
  · exact ⟨⟨0, hzero⟩, isPreconnected_connectedComponentIn⟩

/-- The corrected radius-seven corridor gives uniformly finite constrained
distances from the origin to the radius-five sphere for every Euclidean
length metric. This conclusion uses radius seven and does not establish the
stronger radius-six corridor used by the internal-pinch event. -/
theorem IsCorrectedPinchConfiguration.corridor_internalMetric_lt_top
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) :
    (⨆ y ∈ sphere (0 : ℂ) 5,
      internalMetric D ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 7) 0 y) < ∞ := by
  have hzero : (0 : ℂ) ∈ pinchCorridor W Q δ := h.corridor_contains (Or.inl rfl)
  have hsphere : sphere (0 : ℂ) 5 ⊆ pinchCorridor W Q δ :=
    fun y hy => h.corridor_contains (Or.inr hy)
  obtain ⟨hopen, hconn⟩ := pinchCorridor_open_connected hzero
  apply lt_of_le_of_lt _
    (hD.iSup_internalMetric_lt_top_of_isCompact hnonneg hopen hconn
      (isCompact_sphere (0 : ℂ) 5) hsphere hzero)
  have hsub : pinchCorridor W Q δ ⊆
      (thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 7 := by
    intro x hx
    have hx' := connectedComponentIn_subset
      (ball (0 : ℂ) 7 \ (closure (thickening (2 * δ) Q) ∪
        closure (thickening (2 * δ) W))) 0 hx
    refine ⟨?_, hx'.1⟩
    rw [thickening_union]
    intro hmem
    exact hx'.2 (hmem.elim (fun hq => Or.inl (subset_closure hq))
      (fun hw => Or.inr (subset_closure hw)))
  exact iSup_le fun y => iSup_le fun hy =>
    le_iSup_of_le y (le_iSup_of_le hy (internalMetric_anti D hsub 0 y))

#print axioms IsCorrectedPinchConfiguration.corridor_internalMetric_lt_top
#print axioms IsPinchPointProofConfiguration.sphere_five_avoids_obstacle_closures

end HarmonicBalls
