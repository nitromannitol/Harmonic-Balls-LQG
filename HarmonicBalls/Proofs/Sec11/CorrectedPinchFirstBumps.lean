import HarmonicBalls.Steps.Sec11.PinchSmoothWeylBump

/-! Smooth cutoffs for the two positive Weyl shifts in the first pinch event. -/

namespace HarmonicBalls

open Set Metric Function
open scoped ContDiff

/-- A compact plateau inside an open set admits a smooth compactly supported
cutoff which vanishes outside that open set. -/
theorem exists_smooth_compact_cutoff {K O : Set ℂ}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ x, φ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ K, φ x = 1) ∧ (∀ x ∉ O, φ x = 0) := by
  have hd : Disjoint K Oᶜ := disjoint_left.mpr (fun x hx hxc => hxc (hKO hx))
  obtain ⟨f, hone, hzero, hcompact, _⟩ :=
    exists_continuous_one_zero_of_isCompact hK hO.isClosed_compl hd
  obtain ⟨φ, hsmooth, hφcompact, hrange, hφzero, hφone⟩ :=
    exists_smooth_cutoff_with_same_zero_and_one f hcompact
  exact ⟨φ, hsmooth, hφcompact, hrange,
    fun x hx => hφone x (hone hx), fun x hx => hφzero x (hzero hx)⟩

/-- The root and obstacle cutoffs in the first pinch-event construction. -/
theorem IsPinchPointProofConfiguration.exists_first_weyl_bumps
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) :
    ∃ φQ φ0 : ℂ → ℝ,
      ContDiff ℝ ∞ φQ ∧ HasCompactSupport φQ ∧
      (∀ x, φQ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ closure Q, φQ x = 1) ∧
      (∀ x ∉ thickening δ Q, φQ x = 0) ∧
      ContDiff ℝ ∞ φ0 ∧ HasCompactSupport φ0 ∧
      (∀ x, φ0 x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ closedBall 0 (δ / 2), φ0 x = 1) ∧
      (∀ x ∉ ball 0 δ, φ0 x = 0) := by
  have hδ : 0 < δ := h.δ₀_mem.1
  have hQsub : closure Q ⊆ closure (thickening (10 * δ) Q) :=
    closure_mono (subset_closure.trans (closure_subset_thickening (by linarith) Q))
  have hQcompact : IsCompact (closure Q) := by
    apply isCompact_of_isClosed_isBounded isClosed_closure
    exact isBounded_ball.subset (hQsub.trans (h.thickening_Q.trans sdiff_subset) |>.trans
      (fun _ hx => hx.1))
  obtain ⟨φQ, hQs, hQc, hQr, hQone, hQzero⟩ :=
    exists_smooth_compact_cutoff hQcompact isOpen_thickening
      (closure_subset_thickening hδ Q)
  have hroot : closedBall (0 : ℂ) (δ / 2) ⊆ ball 0 δ := by
    intro x hx
    change dist x 0 < δ
    have hx' : dist x 0 ≤ δ / 2 := hx
    linarith
  obtain ⟨φ0, h0s, h0c, h0r, h0one, h0zero⟩ :=
    exists_smooth_compact_cutoff (isCompact_closedBall 0 (δ / 2)) isOpen_ball hroot
  exact ⟨φQ, φ0, hQs, hQc, hQr, hQone, hQzero,
    h0s, h0c, h0r, h0one, h0zero⟩

#print axioms IsPinchPointProofConfiguration.exists_first_weyl_bumps

end HarmonicBalls
