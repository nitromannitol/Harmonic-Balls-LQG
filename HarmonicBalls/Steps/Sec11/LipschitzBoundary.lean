import HarmonicBalls.Steps.Sec11.LipschitzCone

/-! # Boundary cones for Lipschitz graphs -/

namespace HarmonicBalls

open Complex MeasureTheory Metric Set Filter Topology
open scoped NNReal

/-- A boundary point in a local Lipschitz graph chart lies on the graph. -/
theorem local_lipschitz_graph_boundary_eq
    (A : Set ℂ) (z : ℂ) (r : ℝ) (hr : 0 < r) (e : ℂ ≃ₗᵢ[ℝ] ℂ)
    (K : ℝ≥0) (f : ℝ → ℝ) (hf : LipschitzWith K f)
    (hchart : A ∩ ball z r = {x ∈ ball z r | f (e x).re < (e x).im})
    (hz : z ∈ frontier A) : f (e z).re = (e z).im := by
  let G : Set ℂ := {x | f (e x).re < (e x).im}
  have hzball : z ∈ ball z r := mem_ball_self hr
  have hG : A ∩ ball z r = G ∩ ball z r := by
    rw [hchart]
    ext x
    simp [G, and_comm]
  have hz' : z ∈ frontier (A ∩ ball z r) := by
    have h := (frontier_inter_open_inter (s := A) (t := ball z r) isOpen_ball).symm
    have hz'' : z ∈ frontier A ∩ ball z r := ⟨hz, hzball⟩
    rw [h] at hz''
    exact hz''.1
  rw [hG] at hz'
  have hzG : z ∈ frontier G := by
    have h := frontier_inter_open_inter (s := G) (t := ball z r) isOpen_ball
    have hz'' : z ∈ frontier (G ∩ ball z r) ∩ ball z r := ⟨hz', hzball⟩
    rw [h] at hz''
    exact hz''.1
  exact (frontier_lt_subset_eq (hf.continuous.comp (continuous_re.comp e.continuous))
    (continuous_im.comp e.continuous)) hzG

/-- Every Lipschitz domain satisfies the interior and exterior cone conditions
at each boundary point. -/
theorem IsLipschitzDomain.satisfiesConeCondition {A : Set ℂ}
    (hA : IsLipschitzDomain A) {z : ℂ} (hz : z ∈ frontier A) :
    SatisfiesConeCondition A z := by
  obtain ⟨r, hr, e, K, f, hf, hchart⟩ := hA.2.2 z hz
  have hzgraph := local_lipschitz_graph_boundary_eq A z r hr e K f hf hchart hz
  let k : ℝ := (K : ℝ) + 1
  have hk : 0 < k := by dsimp [k]; positivity
  let W : Set ℂ := {x | k * |x.re| < x.im}
  let Q : Set ℂ := e.symm '' W
  have hQ : IsOpenCone Q := (isOpenCone_verticalWedge hk).linearIsometry_image e.symm
  have hQwedge : ∀ p ∈ Q, k * |(e p).re| < (e p).im := by
    rintro p ⟨y, hy, rfl⟩
    simpa [W] using hy
  have hbound : ∀ p : ℂ,
      |f (e (p + z)).re - f (e z).re| ≤ (K : ℝ) * |(e p).re| := by
    intro p
    have h := hf.dist_le_mul (e (p + z)).re (e z).re
    rw [Real.dist_eq, Real.dist_eq] at h
    have he : (e (p + z)).re - (e z).re = (e p).re := by simp
    rw [he] at h
    exact h
  have hup : ∀ p ∈ Q, f (e (p + z)).re < (e (p + z)).im := by
    intro p hp
    have hw := hQwedge p hp
    have hb := hbound p
    have habs := le_abs_self (f (e (p + z)).re - f (e z).re)
    have hki : 0 ≤ |(e p).re| := abs_nonneg _
    dsimp [k] at hw
    simp only [map_add, add_im] at *
    linarith
  have hdown : ∀ p ∈ Q, (e ((-p) + z)).im ≤ f (e ((-p) + z)).re := by
    intro p hp
    have hw := hQwedge p hp
    have hb := hbound (-p)
    have habs := neg_le_abs (f (e ((-p) + z)).re - f (e z).re)
    have hki : 0 ≤ |(e p).re| := abs_nonneg _
    dsimp [k] at hw
    simp only [map_neg, neg_re, abs_neg, map_add, add_im, neg_im] at *
    linarith
  constructor
  · refine ⟨r, hr, Q, Or.inl hQ, ?_⟩
    rintro x ⟨⟨p, hp, rfl⟩, hx⟩
    have hx' : p + z ∈ A ∩ ball z r := by
      rw [hchart]
      exact ⟨hx, hup p hp⟩
    exact hx'.1
  · refine ⟨r, hr, (fun p : ℂ => -p) '' Q, Or.inl hQ.neg_image, ?_⟩
    rintro x ⟨⟨_, ⟨p, hp, rfl⟩, rfl⟩, hx⟩
    intro hmem
    have hx' : (-p) + z ∈ A ∩ ball z r := ⟨hmem, hx⟩
    rw [hchart] at hx'
    exact (not_lt_of_ge (hdown p hp)) hx'.2

end HarmonicBalls
