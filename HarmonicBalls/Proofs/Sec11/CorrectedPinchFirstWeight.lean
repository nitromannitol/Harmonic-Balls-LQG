import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstBumps
import HarmonicBalls.Proofs.Sec11.CorrectedPinchOpenThresholds

/-! # Weyl weights for the first auxiliary pinch event -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal ContDiff

/-- The first two smooth bumps have the required uniform Weyl exponent bound
on the obstacle-free open corridor. -/
theorem IsPinchPointProofConfiguration.exists_first_weight_corridor_bound
    {U V W T Q' Q : Set ℂ} {δ ξ a b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 ≤ ξ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x) ∧
      (∀ x ∈ ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪
        closure (thickening (2 * δ) W)), ξ * f x ≤ ξ * b) ∧
      (∀ x ∈ closure Q, f x = a) ∧
      (∀ x ∈ closedBall 0 (δ / 2), f x = b) ∧
      (∀ x ∈ thickening δ (T \ thickening (3 * δ) W), f x = 0) ∧
      (∀ x ∉ thickening δ Q ∪ ball 0 δ, f x = 0) := by
  obtain ⟨φQ, φ0, hQs, hQc, hQr, hQone, hQzero,
      h0s, h0c, h0r, h0one, h0zero⟩ := h.exists_first_weyl_bumps
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
      (closure_subset_thickening (by linarith [h.δ₀_mem.1] : 0 < 10 * δ) Q hx))
    have hx0 : x ∉ ball (0 : ℂ) δ := by
      intro hx0
      have hl : 4 < dist x (0 : ℂ) := lt_of_not_ge hxann.1.2
      have hu : dist x (0 : ℂ) < δ := hx0
      linarith [h.δ₀_mem.2]
    simp [f, hQone x hx, h0zero x hx0]
  · intro x hx
    have hxQ : x ∉ thickening δ Q := by
      intro hxQ
      have hxann := h.thickening_Q (subset_closure
        (thickening_mono (by linarith [h.δ₀_mem.1] : δ ≤ 10 * δ) Q hxQ))
      have hl : 4 < dist x (0 : ℂ) := lt_of_not_ge hxann.1.2
      have hu : dist x (0 : ℂ) ≤ δ / 2 := hx
      linarith [h.δ₀_mem.2]
    simp [f, hQzero x hxQ, h0one x hx]
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

/-- The local exponent bounds control both the corridor and outer diameter
after the Weyl shift. -/
theorem IsEuclideanLengthMetric.first_weight_metric_bounds
    {Q W T : Set ℂ} {δ ξ b : ℝ} {f : ℂ → ℝ} {D E : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (hE : IsEuclideanLengthMetric E)
    (hEnonneg : ∀ x y, 0 ≤ E x y)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hcorridor : ∀ z ∈ ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪
      closure (thickening (2 * δ) W)), ξ * f z ≤ ξ * b)
    (houter : ∀ z ∈ thickening δ (T \ thickening (3 * δ) W), f z = 0) :
    (⨆ y ∈ sphere (0 : ℂ) 5,
      internalMetric E ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 y) ≤
      ENNReal.ofReal (Real.exp (ξ * b)) * (⨆ y ∈ sphere (0 : ℂ) 5,
        internalMetric D (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
          closure (thickening (2 * δ) W))) 0 y) ∧
    internalDiam E δ (T \ thickening (3 * δ) W) ≤
      internalDiam D δ (T \ thickening (3 * δ) W) := by
  refine ⟨hD.six_corridor_weyl_upper_bound hE hEnonneg hscale hcorridor, ?_⟩
  have hd := hD.internalDiam_weylScaling_le hE hEnonneg (T \ thickening (3 * δ) W)
    (hD.weylScaling_zero ξ) hscale (B := 0) (δ := δ) (by
      intro z hz
      simp [houter z hz])
  simpa using hd


end HarmonicBalls
