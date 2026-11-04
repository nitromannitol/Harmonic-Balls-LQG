import HarmonicBalls.Proofs.Sec6.FiniteGraphChains
import HarmonicBalls.Proofs.Sec6.HarnackCoverComparison

/-! # Scale-uniform Harnack inequality on planar annuli -/

namespace HarmonicBalls.Section6

open Metric Set InnerProductSpace

/-- Nonnegative harmonic functions have uniformly comparable values on a
concentric subannulus, with a constant depending only on the four radii. -/
theorem exists_uniform_annulus_harnack {s₁ s₂ s₃ s₄ : ℝ}
    (h1 : 0 < s₁) (h12 : s₁ < s₂) (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ), 0 < ρ → ∀ (c : ℂ) (f : ℂ → ℝ),
      HarmonicOnNhd f (annulus c (s₁ * ρ) (s₄ * ρ)) →
      (∀ z ∈ annulus c (s₁ * ρ) (s₄ * ρ), 0 ≤ f z) →
      ∀ x ∈ annulus c (s₂ * ρ) (s₃ * ρ),
      ∀ y ∈ annulus c (s₂ * ρ) (s₃ * ρ), f x ≤ C * f y := by
  obtain ⟨δ, hδ, T, _, _, hcover, hdisc, N, hgraph⟩ :=
    exists_uniform_middle_annulus_cover_graph h1 h12 h23 h34
  refine ⟨(16 : ℝ) ^ (N + 1), by positivity, ?_⟩
  intro ρ hρ c f hf hnonneg x hx y hy
  have hdist (a b : ℂ) : dist (ρ • a + c) (ρ • b + c) = ρ * dist a b := by
    rw [dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ]
  have hdist0 (a : ℂ) : dist (ρ • a + c) c = ρ * dist a 0 := by
    simpa only [smul_zero, zero_add] using hdist a 0
  have hback (z : ℂ) : ρ • (ρ⁻¹ • (z - c)) + c = z := by
    simp only [smul_inv_smul₀ hρ.ne', sub_add_cancel]
  have hann (a : ℂ) (s t : ℝ) :
      (ρ • a + c ∈ annulus c (s * ρ) (t * ρ)) ↔ a ∈ annulus 0 s t := by
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le, hdist0]
    constructor <;> intro h <;> constructor <;> nlinarith
  let x' := ρ⁻¹ • (x - c)
  let y' := ρ⁻¹ • (y - c)
  have hx' : x' ∈ annulus 0 s₂ s₃ := (hann x' s₂ s₃).1 (by simpa only [x', hback] using hx)
  have hy' : y' ∈ annulus 0 s₂ s₃ := (hann y' s₂ s₃).1 (by simpa only [y', hback] using hy)
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp (hcover hx')
  obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp (hcover hy')
  obtain ⟨p, hp0, hpN, hstep⟩ := hgraph v hv u hu
  let q : ℕ → ℂ := fun i => ρ • p i + c
  have hpT : ∀ i ≤ N, p i ∈ T := by
    intro i hi
    by_cases hlt : i < N
    · exact (hstep i hlt).1
    · have : i = N := by omega
      subst i
      simpa [hpN] using hu
  have hqdisc : ∀ i ≤ N, closedBall (q i) (2 * (ρ * δ)) ⊆ annulus c (s₁ * ρ) (s₄ * ρ) := by
    intro i hi z hz
    let z' := ρ⁻¹ • (z - c)
    have hclose : dist z' (p i) ≤ 2 * δ := by
      have h := mem_closedBall.mp hz
      change dist z (ρ • p i + c) ≤ 2 * (ρ * δ) at h
      rw [← hback z, hdist] at h
      nlinarith
    have hunit := hdisc (p i) (hpT i hi) (mem_closedBall.mpr hclose)
    have h := (hann z' s₁ s₄).2 hunit
    simpa only [z', hback] using h
  have hqstep : ∀ i < N, (ball (q i) (ρ * δ) ∩ ball (q (i + 1)) (ρ * δ)).Nonempty := by
    intro i hi
    obtain ⟨z, hz1, hz2⟩ := (hstep i hi).2.2
    refine ⟨ρ • z + c, ?_, ?_⟩
    · change dist (ρ • z + c) (ρ • p i + c) < ρ * δ
      rw [hdist]
      exact mul_lt_mul_of_pos_left (mem_ball.mp hz1) hρ
    · change dist (ρ • z + c) (ρ • p (i + 1) + c) < ρ * δ
      rw [hdist]
      exact mul_lt_mul_of_pos_left (mem_ball.mp hz2) hρ
  have hqx : x ∈ ball (q N) (ρ * δ) := by
    change dist x (ρ • p N + c) < ρ * δ
    rw [hpN, ← hback x, hdist]
    exact mul_lt_mul_of_pos_left (mem_ball.mp hxu) hρ
  have hqy : y ∈ ball (q 0) (ρ * δ) := by
    change dist y (ρ • p 0 + c) < ρ * δ
    rw [hp0, ← hback y, hdist]
    exact mul_lt_mul_of_pos_left (mem_ball.mp hyv) hρ
  exact harmonic_le_of_intersecting_disc_chain_endpoints hf hnonneg (mul_pos hρ hδ)
    q N hqdisc hqstep hqx hqy

end HarmonicBalls.Section6
