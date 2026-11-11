import HarmonicBalls.Proofs.Sec10.CountableDeletionCrossings
import HarmonicBalls.Proofs.Sec11.CorrectedPinchOuterDisk

/-! # Removing a compactly contained disk from a planar domain -/

namespace HarmonicBalls
open Set Metric

/-- Removing a disk whose closure lies in an open connected planar set
leaves a connected set. -/
theorem isConnected_sdiff_ball_of_closure_subset
    {T : Set ℂ} (hT : IsOpen T) (hTc : IsConnected T)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (hsub : closure (ball c r) ⊆ T) :
    IsConnected (T \ ball c r) := by
  let f : ℂ → ℂ := fun z => c + (max r ‖z - c‖ / ‖z - c‖) • (z - c)
  let S : Set ℂ := T \ {c}
  have hS : IsPreconnected S :=
    isPreconnected_sdiff_countable_of_isOpen hT hTc.isPreconnected
      ((countable_singleton c).mono inter_subset_left)
  have hnonzero : ∀ z ∈ S, ‖z - c‖ ≠ 0 := by
    intro z hz
    simp only [norm_ne_zero_iff, sub_ne_zero]
    exact hz.2
  have hc : ContinuousOn f S := by
    have hd : ContinuousOn (fun z : ℂ => ‖z - c‖) S := by fun_prop
    have hn : Continuous (fun z : ℂ => max r ‖z - c‖) := by fun_prop
    have hq : ContinuousOn (fun z : ℂ => max r ‖z - c‖ / ‖z - c‖) S :=
      hn.continuousOn.div hd hnonzero
    exact continuousOn_const.add (hq.smul (by fun_prop))
  have hdist : ∀ z ∈ S, dist (f z) c = max r ‖z - c‖ := by
    intro z hz
    have hn : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.2)
    have hq : 0 ≤ max r ‖z - c‖ / ‖z - c‖ := div_nonneg (le_max_of_le_left hr.le) hn.le
    rw [dist_eq_norm]
    change ‖c + (max r ‖z - c‖ / ‖z - c‖) • (z - c) - c‖ = _
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
    exact div_mul_cancel₀ _ hn.ne'
  have himage : f '' S = T \ ball c r := by
    apply Subset.antisymm
    · rintro z ⟨w, hw, rfl⟩
      have hd := hdist w hw
      refine ⟨?_, ?_⟩
      · by_cases hwball : w ∈ ball c r
        · apply hsub
          rw [closure_ball c hr.ne', mem_closedBall, hd]
          have hwlt : ‖w - c‖ < r := by simpa [mem_ball, dist_eq_norm] using hwball
          rw [max_eq_left hwlt.le]
        · have hwle : r ≤ ‖w - c‖ := by
            simpa [mem_ball, dist_eq_norm, not_lt] using hwball
          have hf : f w = w := by
            dsimp [f]
            rw [max_eq_right hwle, div_self (hnonzero w hw), Complex.ofReal_one, one_mul, add_sub_cancel]
          rw [hf]
          exact hw.1
      · rw [mem_ball, hd]
        exact not_lt_of_ge (le_max_left _ _)
    · intro z hz
      have hzle : r ≤ ‖z - c‖ := by
        simpa [mem_ball, dist_eq_norm, not_lt] using hz.2
      have hzc : z ≠ c := by
        intro heq
        subst z
        simp at hzle
        linarith
      have hzS : z ∈ S := ⟨hz.1, hzc⟩
      refine ⟨z, hzS, ?_⟩
      dsimp [f]
      rw [max_eq_right hzle, div_self (hnonzero z hzS), Complex.ofReal_one, one_mul, add_sub_cancel]
  have hpre : IsPreconnected (T \ ball c r) := by
    rw [← himage]
    exact hS.image f hc
  obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty (x := c)).mpr hr.le
  have hzT : z ∈ T := hsub (by rw [closure_ball c hr.ne']; exact sphere_subset_closedBall hz)
  have hzb : z ∉ ball c r := by
    rw [mem_ball, mem_sphere] at *
    linarith
  exact ⟨⟨z, hzT, hzb⟩, hpre⟩

/-- The corrected configuration's outer auxiliary piece is connected. -/
theorem IsCorrectedPinchConfiguration.outer_piece_isConnected
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    IsConnected (T \ thickening (3 * δ) W) := by
  obtain ⟨c, r, hr, heq, hsub⟩ := h.exists_outer_removed_disk
  rw [heq]
  exact isConnected_sdiff_ball_of_closure_subset h.isOpen_T h.isConnected_T c hr hsub

end HarmonicBalls
