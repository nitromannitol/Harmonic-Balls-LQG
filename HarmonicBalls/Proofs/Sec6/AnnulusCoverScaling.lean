import HarmonicBalls.Proofs.Sec6.AnnulusFiniteCover

/-! # Scale-independent annulus covers

The disc cover used in Lemma 6.8 can be chosen uniformly over all centres
and positive scales by transporting one finite unit-scale cover.
-/

namespace HarmonicBalls.Section6

open Set Metric

private theorem dist_affine (r : ℝ) (w a b : ℂ) (hr : 0 < r) :
    dist (r • a + w) (r • b + w) = r * dist a b := by
  rw [dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr]

/-- A single finite set of unit-scale centres covers all translated and scaled
middle annuli, with doubled closed discs inside the corresponding outer annuli. -/
theorem exists_uniform_scaled_annulus_cover {s₁ s₂ s₃ s₄ : ℝ}
    (h12 : s₁ < s₂) (h34 : s₃ < s₄) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ T : Set ℂ, T.Finite ∧
      T ⊆ annulus 0 s₂ s₃ ∧
      ∀ (w : ℂ) (r : ℝ), 0 < r →
        (∀ x ∈ T, r • x + w ∈ annulus w (s₂ * r) (s₃ * r)) ∧
        (annulus w (s₂ * r) (s₃ * r) ⊆ ⋃ x ∈ T, ball (r • x + w) (δ * r)) ∧
        (∀ x ∈ T, closedBall (r • x + w) (2 * δ * r) ⊆
          annulus w (s₁ * r) (s₄ * r)) := by
  obtain ⟨δ, hδ, T, hTf, hTs, hcov, houter⟩ :=
    exists_finite_middle_annulus_cover h12 h34
  refine ⟨δ, hδ, T, hTf, hTs, ?_⟩
  intro w r hr
  have hdist (a b : ℂ) : dist (r • a + w) (r • b + w) = r * dist a b :=
    dist_affine r w a b hr
  have hdist0 (a : ℂ) : dist (r • a + w) w = r * dist a 0 := by
    simpa only [smul_zero, zero_add] using hdist a 0
  have hback (y : ℂ) : r • (r⁻¹ • (y - w)) + w = y := by
    simp only [smul_inv_smul₀ hr.ne', sub_add_cancel]
  have hann (a : ℂ) (s t : ℝ) :
      (r • a + w ∈ annulus w (s * r) (t * r)) ↔ a ∈ annulus 0 s t := by
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le, hdist0]
    constructor <;> intro h <;> constructor <;> nlinarith
  constructor
  · intro x hx
    exact (hann x s₂ s₃).2 (hTs hx)
  constructor
  · intro y hy
    let a := r⁻¹ • (y - w)
    have ha : a ∈ annulus 0 s₂ s₃ := (hann a s₂ s₃).1 (by simpa only [a, hback] using hy)
    obtain ⟨x, hx, hax⟩ := mem_iUnion₂.mp (hcov ha)
    refine mem_iUnion₂.mpr ⟨x, hx, ?_⟩
    have hball : dist a x < δ := mem_ball.mp hax
    apply mem_ball.mpr
    rw [← hback y, hdist]
    nlinarith
  · intro x hx y hy
    let a := r⁻¹ • (y - w)
    have hball : dist a x ≤ 2 * δ := by
      have h := mem_closedBall.mp hy
      rw [← hback y, hdist] at h
      nlinarith
    have ha := houter x hx (mem_closedBall.mpr hball)
    have := (hann a s₁ s₄).2 ha
    simpa only [a, hback] using this

end HarmonicBalls.Section6
