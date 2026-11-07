import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstBumps
import HarmonicBalls.Proofs.Sec11.CorrectedPinchOpenThresholds

/-! # Weyl weights for the first auxiliary pinch event -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal ContDiff

/-- Smooth root and obstacle cutoffs with room around each plateau. -/
theorem IsPinchPointProofConfiguration.exists_first_weyl_bumps_buffered
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) :
    ∃ φQ φ0 : ℂ → ℝ,
      ContDiff ℝ ∞ φQ ∧ HasCompactSupport φQ ∧
      (∀ x, φQ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ closure (thickening (δ / 2) Q), φQ x = 1) ∧
      (∀ x ∉ thickening δ Q, φQ x = 0) ∧
      ContDiff ℝ ∞ φ0 ∧ HasCompactSupport φ0 ∧
      (∀ x, φ0 x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ closedBall 0 (3 * δ / 4), φ0 x = 1) ∧
      (∀ x ∉ ball 0 δ, φ0 x = 0) := by
  have hδ : 0 < δ := h.δ₀_mem.1
  have hQsub : closure (thickening (δ / 2) Q) ⊆
      closure (thickening (10 * δ) Q) :=
    closure_mono (thickening_mono (by linarith) Q)
  have hQcompact : IsCompact (closure (thickening (δ / 2) Q)) := by
    apply isCompact_of_isClosed_isBounded isClosed_closure
    exact isBounded_ball.subset (hQsub.trans (h.thickening_Q.trans sdiff_subset) |>.trans
      (fun _ hx => hx.1))
  have hQinside : closure (thickening (δ / 2) Q) ⊆ thickening δ Q :=
    (closure_thickening_subset_cthickening (δ / 2) Q).trans
      (cthickening_subset_thickening' hδ (by linarith) Q)
  obtain ⟨φQ, hQs, hQc, hQr, hQone, hQzero⟩ :=
    exists_smooth_compact_cutoff hQcompact isOpen_thickening hQinside
  have hroot : closedBall (0 : ℂ) (3 * δ / 4) ⊆ ball 0 δ := by
    intro x hx
    change dist x 0 < δ
    have hx' : dist x 0 ≤ 3 * δ / 4 := hx
    linarith
  obtain ⟨φ0, h0s, h0c, h0r, h0one, h0zero⟩ :=
    exists_smooth_compact_cutoff (isCompact_closedBall 0 (3 * δ / 4)) isOpen_ball hroot
  exact ⟨φQ, φ0, hQs, hQc, hQr, hQone, hQzero,
    h0s, h0c, h0r, h0one, h0zero⟩

/-- The first two smooth bumps have the required uniform Weyl exponent bound
on the obstacle-free open corridor. -/
theorem IsPinchPointProofConfiguration.exists_first_buffered_weight_corridor_bound
    {U V W T Q' Q : Set ℂ} {δ ξ a b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 ≤ ξ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x) ∧
      (∀ x ∈ ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪
        closure (thickening (2 * δ) W)), ξ * f x ≤ ξ * b) ∧
      (∀ x ∈ thickening (δ / 2) Q, f x = a) ∧
      (∀ x ∈ ball 0 (3 * δ / 4), f x = b) ∧
      (∀ x ∈ thickening δ (T \ thickening (3 * δ) W), f x = 0) ∧
      (∀ x ∉ thickening δ Q ∪ ball 0 δ, f x = 0) := by
  obtain ⟨φQ, φ0, hQs, hQc, hQr, hQone, hQzero,
      h0s, h0c, h0r, h0one, h0zero⟩ := h.exists_first_weyl_bumps_buffered
  let f : ℂ → ℝ := fun x => a * φQ x + b * φ0 x
  refine ⟨f, (contDiff_const.mul hQs).add (contDiff_const.mul h0s),
    hQc.mul_left.add h0c.mul_left, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact add_nonneg (mul_nonneg ha (hQr x).1) (mul_nonneg hb (h0r x).1)
  · intro x hx
    have hxQ : x ∉ thickening δ Q := by
      intro hxQ
      have hx2 : x ∈ thickening (2 * δ) Q :=
        thickening_mono (by linarith [h.δ₀_mem.1]) Q hxQ
      exact hx.2 (Or.inl (subset_closure hx2))
    have hle : f x ≤ b := by
      dsimp [f]
      rw [hQzero x hxQ]
      simpa using mul_le_mul_of_nonneg_left (h0r x).2 hb
    exact mul_le_mul_of_nonneg_left hle hξ
  · intro x hx
    have hxann := h.thickening_Q (subset_closure
      (thickening_mono (by linarith [h.δ₀_mem.1] : δ / 2 ≤ 10 * δ) Q hx))
    have hx0 : x ∉ ball (0 : ℂ) δ := by
      intro hx0
      have hl : 4 < dist x (0 : ℂ) := lt_of_not_ge hxann.1.2
      have hu : dist x (0 : ℂ) < δ := hx0
      linarith [h.δ₀_mem.2]
    simp [f, hQone x (subset_closure hx), h0zero x hx0]
  · intro x hx
    have hxQ : x ∉ thickening δ Q := by
      intro hxQ
      have hxann := h.thickening_Q (subset_closure
        (thickening_mono (by linarith [h.δ₀_mem.1] : δ ≤ 10 * δ) Q hxQ))
      have hl : 4 < dist x (0 : ℂ) := lt_of_not_ge hxann.1.2
      have hu : dist x (0 : ℂ) < 3 * δ / 4 := hx
      linarith [h.δ₀_mem.2]
    simp [f, hQzero x hxQ, h0one x (show x ∈ closedBall 0 (3 * δ / 4) from
      le_of_lt (show dist x 0 < 3 * δ / 4 from hx))]
  · intro x hx
    have hxT : x ∈ thickening (10 * δ) T :=
      thickening_mono (by linarith [h.δ₀_mem.1]) T
        (thickening_subset_of_subset δ sdiff_subset hx)
    have hxQ : x ∉ thickening δ Q := by
      intro hxQ
      have hn := (h.thickening_Q (subset_closure
        (thickening_mono (by linarith [h.δ₀_mem.1] : δ ≤ 10 * δ) Q hxQ))).2
      exact hn hxT
    have hx0 : x ∉ ball (0 : ℂ) δ := by
      intro hx0
      have hann := h.thickening_T (subset_closure hxT)
      have hl : 1 < dist x (0 : ℂ) := lt_of_not_ge hann.2
      have hu : dist x (0 : ℂ) < δ := hx0
      linarith [h.δ₀_mem.2]
    simp [f, hQzero x hxQ, h0zero x hx0]
  · intro x hx
    have hq : x ∉ thickening δ Q := fun hxq => hx (Or.inl hxq)
    have h0 : x ∉ ball (0 : ℂ) δ := fun hx0 => hx (Or.inr hx0)
    simp [f, hQzero x hq, h0zero x h0]


#print axioms IsPinchPointProofConfiguration.exists_first_weyl_bumps_buffered
#print axioms IsPinchPointProofConfiguration.exists_first_buffered_weight_corridor_bound

end HarmonicBalls
