import HarmonicBalls.Proofs.Sec6.HarnackChain

/-! # Scaling planar Harnack chains

A chain in a unit-scale annulus transports to every positive scale and centre.
-/

namespace HarmonicBalls.Section6

open Metric Set

/-- Translation and positive dilation carry a Harnack chain in a unit-scale
annulus to the corresponding chain in the scaled annulus. -/
theorem harnack_chain_scale {a b r : ℝ} (p : ℕ → ℂ) (n : ℕ)
    (hdisc : ∀ i < n, closedBall (p i) r ⊆ annulus 0 a b)
    (hstep : ∀ i < n, p (i + 1) ∈ closedBall (p i) (r / 2))
    (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∀ i < n, closedBall (ρ • p i + c) (ρ * r) ⊆
      annulus c (a * ρ) (b * ρ)) ∧
    (∀ i < n, ρ • p (i + 1) + c ∈ closedBall (ρ • p i + c) ((ρ * r) / 2)) := by
  have hdist (x y : ℂ) : dist (ρ • x + c) (ρ • y + c) = ρ * dist x y := by
    rw [dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ]
  have hdist0 (x : ℂ) : dist (ρ • x + c) c = ρ * dist x 0 := by
    simpa only [smul_zero, zero_add] using hdist x 0
  have hback (y : ℂ) : ρ • (ρ⁻¹ • (y - c)) + c = y := by
    simp only [smul_inv_smul₀ hρ.ne', sub_add_cancel]
  have hann (x : ℂ) :
      (ρ • x + c ∈ annulus c (a * ρ) (b * ρ)) ↔ x ∈ annulus 0 a b := by
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le, hdist0]
    constructor <;> intro h <;> constructor <;> nlinarith
  constructor
  · intro i hi y hy
    let x := ρ⁻¹ • (y - c)
    have hclose : dist x (p i) ≤ r := by
      have h := mem_closedBall.mp hy
      rw [← hback y, hdist] at h
      nlinarith
    have hx := hdisc i hi (mem_closedBall.mpr hclose)
    have h := (hann x).2 hx
    simpa only [x, hback] using h
  · intro i hi
    apply mem_closedBall.mpr
    rw [hdist]
    have h := mem_closedBall.mp (hstep i hi)
    nlinarith

/-- Uniform unit-scale chains give uniform chains for all centres and scales. -/
theorem harnack_chains_scale {a b a' b' r : ℝ} (N : ℕ)
    (hchains : ∀ x ∈ annulus 0 a' b', ∀ y ∈ annulus 0 a' b',
      ∃ p : ℕ → ℂ, p 0 = y ∧ p N = x ∧
        (∀ i < N, closedBall (p i) r ⊆ annulus 0 a b) ∧
        (∀ i < N, p (i + 1) ∈ closedBall (p i) (r / 2)))
    (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ x ∈ annulus c (a' * ρ) (b' * ρ),
    ∀ y ∈ annulus c (a' * ρ) (b' * ρ),
      ∃ p : ℕ → ℂ, p 0 = y ∧ p N = x ∧
        (∀ i < N, closedBall (p i) (ρ * r) ⊆ annulus c (a * ρ) (b * ρ)) ∧
        (∀ i < N, p (i + 1) ∈ closedBall (p i) ((ρ * r) / 2)) := by
  have hdist0 (x : ℂ) : dist (ρ • x + c) c = ρ * dist x 0 := by
    simpa only [smul_zero, zero_add] using
      (show dist (ρ • x + c) (ρ • (0 : ℂ) + c) = ρ * dist x 0 by
        rw [dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ])
  have hback (y : ℂ) : ρ • (ρ⁻¹ • (y - c)) + c = y := by
    simp only [smul_inv_smul₀ hρ.ne', sub_add_cancel]
  have hann (x : ℂ) :
      (ρ • x + c ∈ annulus c (a' * ρ) (b' * ρ)) ↔ x ∈ annulus 0 a' b' := by
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le, hdist0]
    constructor <;> intro h <;> constructor <;> nlinarith
  intro x hx y hy
  let x' := ρ⁻¹ • (x - c)
  let y' := ρ⁻¹ • (y - c)
  have hx' : x' ∈ annulus 0 a' b' := (hann x').1 (by simpa only [x', hback] using hx)
  have hy' : y' ∈ annulus 0 a' b' := (hann y').1 (by simpa only [y', hback] using hy)
  obtain ⟨p, hp0, hpN, hdisc, hstep⟩ := hchains x' hx' y' hy'
  refine ⟨fun i => ρ • p i + c, ?_, ?_, harnack_chain_scale p N hdisc hstep c hρ⟩
  · simp only [hp0, y', hback]
  · simp only [hpN, x', hback]

end HarmonicBalls.Section6
