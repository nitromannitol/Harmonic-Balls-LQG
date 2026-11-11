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

/-- Radial clipping transfers the radius-seven component to an obstacle-free
connected subset of the radius-six ball, preserving the origin and sphere. -/
theorem IsCorrectedPinchConfiguration.sphere_subset_six_component
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    sphere (0 : ℂ) 5 ⊆ connectedComponentIn
      (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
        closure (thickening (2 * δ) W))) 0 := by
  let R : ℝ := 11 / 2
  let f : ℂ → ℂ := fun x => (R / max R ‖x‖) • x
  have hR : 0 < R := by norm_num [R]
  have hfcont : Continuous f := by
    have hc : Continuous (fun x : ℂ => R / max R ‖x‖) := by
      apply Continuous.div continuous_const (continuous_const.max continuous_norm)
      intro x
      exact ne_of_gt (lt_of_lt_of_le hR (le_max_left _ _))
    exact hc.smul continuous_id
  have hfix : ∀ x : ℂ, ‖x‖ ≤ R → f x = x := by
    intro x hx
    simp [f, max_eq_left hx, ne_of_gt hR]
  have hnorm : ∀ x : ℂ, ‖f x‖ ≤ R := by
    intro x
    by_cases hx : ‖x‖ ≤ R
    · rw [hfix x hx]; exact hx
    · have hxR : R < ‖x‖ := lt_of_not_ge hx
      have hx0 : ‖x‖ ≠ 0 := ne_of_gt (lt_trans hR hxR)
      simp only [f, max_eq_right (le_of_lt hxR), norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hR (lt_trans hR hxR))]
      rw [div_mul_cancel₀ R hx0]
  have hout : ∀ x : ℂ, R < ‖x‖ → f x ∉ ball (0 : ℂ) 5 := by
    intro x hx
    have hx0 : ‖x‖ ≠ 0 := ne_of_gt (lt_trans hR hx)
    have hn : ‖f x‖ = R := by
      simp only [f, max_eq_right (le_of_lt hx), norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hR (lt_trans hR hx))]
      exact div_mul_cancel₀ R hx0
    simp only [mem_ball, dist_zero_right, not_lt]
    rw [hn]
    norm_num [R]
  let C := pinchCorridor W Q δ
  let F : Set ℂ := ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
    closure (thickening (2 * δ) W))
  have hz : (0 : ℂ) ∈ C := h.corridor_contains (Or.inl rfl)
  have hCsub : C ⊆ ball (0 : ℂ) 7 \ (closure (thickening (2 * δ) Q) ∪
      closure (thickening (2 * δ) W)) := connectedComponentIn_subset _ _
  have himage : f '' C ⊆ F := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [mem_ball, dist_zero_right]
      have := hnorm x
      dsimp [R] at this
      linarith
    · by_cases hxr : ‖x‖ ≤ R
      · rw [hfix x hxr]
        exact (hCsub hx).2
      · intro hobs
        exact hout x (lt_of_not_ge hxr)
          (h.toIsPinchPointProofConfiguration.obstacle_closures_subset_ball_five hobs)
  have hzero : (0 : ℂ) ∈ f '' C := by
    exact ⟨0, hz, hfix 0 (by norm_num [R])⟩
  have hconn : IsPreconnected (f '' C) :=
    isPreconnected_connectedComponentIn.image f hfcont.continuousOn
  have hsub := hconn.subset_connectedComponentIn hzero himage
  intro y hy
  apply hsub
  refine ⟨y, h.corridor_contains (Or.inr hy), ?_⟩
  apply hfix
  rw [mem_sphere, dist_zero_right] at hy
  rw [hy]
  norm_num [R]

/-- The corrected corridor also supplies the radius-six constrained
finiteness needed by the internal-pinch event. -/
theorem IsCorrectedPinchConfiguration.six_corridor_internalMetric_lt_top
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) :
    (⨆ y ∈ sphere (0 : ℂ) 5,
      internalMetric D ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 y) < ∞ := by
  let F : Set ℂ := ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
    closure (thickening (2 * δ) W))
  let C := connectedComponentIn F (0 : ℂ)
  have hsphere : sphere (0 : ℂ) 5 ⊆ C := h.sphere_subset_six_component
  obtain ⟨y, hy⟩ := NormedSpace.sphere_nonempty (x := (0 : ℂ)) |>.mpr (by norm_num : (0 : ℝ) ≤ 5)
  have hzeroF : (0 : ℂ) ∈ F := connectedComponentIn_nonempty_iff.mp ⟨y, hsphere hy⟩
  have hzero : (0 : ℂ) ∈ C := mem_connectedComponentIn hzeroF
  have hopen : IsOpen C :=
    (isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)).connectedComponentIn
  have hconn : IsConnected C := ⟨⟨0, hzero⟩, isPreconnected_connectedComponentIn⟩
  apply hD.pinch_constrained_iSup_lt_top_of_corridor hnonneg hopen hconn hzero hsphere
  intro x hx
  have hx' := connectedComponentIn_subset F 0 hx
  refine ⟨?_, hx'.1⟩
  rw [thickening_union]
  intro hmem
  exact hx'.2 (hmem.elim (fun hq => Or.inl (subset_closure hq))
    (fun hw => Or.inr (subset_closure hw)))

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


end HarmonicBalls
