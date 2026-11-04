import HarmonicBalls.Draft.Section11

/-! # Containment of the auxiliary pinch pieces

The buffer in the proof configuration keeps the pieces and their
neighborhoods inside the radius-six ball.
-/

namespace HarmonicBalls

open Set Metric

/-- The three auxiliary pieces and their δ-neighborhoods lie in `B₆`. -/
theorem IsPinchPointProofConfiguration.auxiliary_piece_containments
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) :
    closure (T \ thickening (3 * δ) W) ⊆ ball 0 6 ∧
    closure (thickening (3 * δ) W \ V) ⊆ ball 0 6 ∧
    closure V ⊆ ball 0 6 ∧
    thickening δ (T \ thickening (3 * δ) W) ⊆ ball 0 6 ∧
    thickening δ (thickening (3 * δ) W \ V) ⊆ ball 0 6 ∧
    thickening δ V ⊆ ball 0 6 := by
  have hδ : 0 < δ := h.δ₀_mem.1
  have hT : closure (thickening (10 * δ) T) ⊆ ball 0 6 := by
    exact h.thickening_T.trans (by intro x hx; exact hx.1)
  have hW : closure (thickening (10 * δ) W) ⊆ ball 0 6 := by
    intro x hx
    have hx' := h.thickening_W hx
    exact Metric.ball_subset_ball (by norm_num : (2 : ℝ) ≤ 6) hx'.1
  have hVT : V ⊆ T := by
    exact (subset_closure.trans h.closure_V_subset_W).trans
      (subset_closure.trans h.closure_W_subset_T)
  have hclT : closure T ⊆ ball 0 6 :=
    (closure_subset_thickening (by positivity : 0 < 10 * δ) T).trans
      (subset_closure.trans hT)
  have hclW3 : closure (thickening (3 * δ) W) ⊆ ball 0 6 :=
    (closure_mono (thickening_mono (by linarith : 3 * δ ≤ 10 * δ) W)).trans hW
  have hthT : thickening δ T ⊆ ball 0 6 :=
    (thickening_mono (by linarith : δ ≤ 10 * δ) T).trans (subset_closure.trans hT)
  have hthW : thickening δ (thickening (3 * δ) W) ⊆ ball 0 6 :=
    (thickening_thickening_subset δ (3 * δ) W).trans
      ((thickening_mono (by linarith : δ + 3 * δ ≤ 10 * δ) W).trans
        (subset_closure.trans hW))
  exact ⟨(closure_mono sdiff_subset).trans hclT,
    (closure_mono sdiff_subset).trans hclW3,
    (closure_mono hVT).trans hclT,
    (thickening_subset_of_subset δ sdiff_subset).trans hthT,
    (thickening_subset_of_subset δ sdiff_subset).trans hthW,
    (thickening_subset_of_subset δ hVT).trans hthT⟩

/-- The closure of `V` meets the closure of the surrounding auxiliary piece. -/
theorem IsPinchPointProofConfiguration.inner_auxiliary_pieces_meet
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) :
    (closure (thickening (3 * δ) W \ V) ∩ closure V).Nonempty := by
  have hU : U.Nonempty := h.isConnected_U.nonempty
  have hV : V.Nonempty := hU.mono (subset_closure.trans h.closure_U_subset_V)
  have hVne : V ≠ univ := by
    intro heq
    have hz : (0 : ℂ) ∈ V := by rw [heq]; exact mem_univ _
    have hz' := h.V_subset hz
    exact hz'.2 (by simp)
  obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr ⟨hV, hVne⟩
  have hxV : x ∈ closure V := frontier_subset_closure hx
  have hxW : x ∈ W := h.closure_V_subset_W hxV
  have hxth : x ∈ thickening (3 * δ) W :=
    self_subset_thickening (by linarith [h.δ₀_mem.1]) W hxW
  have hxcompl : x ∈ closure Vᶜ := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  have hxpiece : x ∈ closure (thickening (3 * δ) W \ V) := by
    exact isOpen_thickening.inter_closure ⟨hxth, hxcompl⟩
  exact ⟨x, hxpiece, hxV⟩

/-- Connectedness of `T` forces the outer auxiliary piece to meet the
surrounding piece at the boundary of the thickened `W`. -/
theorem IsPinchPointProofConfiguration.outer_auxiliary_pieces_meet
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) :
    (closure (T \ thickening (3 * δ) W) ∩
      closure (thickening (3 * δ) W \ V)).Nonempty := by
  let O := thickening (3 * δ) W
  have hδ := h.δ₀_mem.1
  have hWO : W ⊆ O := self_subset_thickening (by linarith) W
  have hVO : closure V ⊆ O := h.closure_V_subset_W.trans hWO
  have hOT : (T ∩ O).Nonempty := by
    obtain ⟨x, hx⟩ := h.isConnected_U.nonempty
    have hxV : x ∈ V := h.closure_U_subset_V (subset_closure hx)
    have hxW : x ∈ W := h.closure_V_subset_W (subset_closure hxV)
    exact ⟨x, h.closure_W_subset_T (subset_closure hxW), hWO hxW⟩
  have hO2 : O ⊆ ball (0 : ℂ) 2 := by
    intro x hx
    have hx' : x ∈ closure (thickening (10 * δ) W) :=
      subset_closure (thickening_mono (by linarith) W hx)
    exact (h.thickening_W hx').1
  have hnot : ¬ T ⊆ O := by
    intro hTO
    have hc : closure T ⊆ closedBall (0 : ℂ) 2 :=
      closure_minimal (hTO.trans (hO2.trans ball_subset_closedBall)) isClosed_closedBall
    obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (x := (0 : ℂ)) |>.mpr (by norm_num : (0 : ℝ) ≤ 5)
    have hxcl : x ∈ closure T := frontier_subset_closure (h.sphere_subset_frontier hx)
    have hx2 := hc hxcl
    rw [mem_sphere] at hx
    rw [mem_closedBall] at hx2
    linarith
  have hbound : ∃ x ∈ closure O ∩ T, x ∉ O := by
    by_contra hn
    apply hnot
    apply h.isConnected_T.isPreconnected.subset_of_closure_inter_subset isOpen_thickening hOT
    intro x hx
    by_contra hxo
    exact hn ⟨x, hx, hxo⟩
  obtain ⟨x, ⟨hxcl, hxT⟩, hxO⟩ := hbound
  have hxV : x ∉ closure V := fun hv => hxO (hVO hv)
  have hxB : x ∈ closure (O \ V) := by
    have hopen : IsOpen ((closure V)ᶜ) := isClosed_closure.isOpen_compl
    have hx : x ∈ closure ((closure V)ᶜ ∩ O) := hopen.inter_closure ⟨hxV, hxcl⟩
    apply (closure_mono ?_) hx
    intro y hy
    exact ⟨hy.2, fun hyV => hy.1 (subset_closure hyV)⟩
  exact ⟨x, subset_closure ⟨hxT, hxO⟩, hxB⟩

end HarmonicBalls
