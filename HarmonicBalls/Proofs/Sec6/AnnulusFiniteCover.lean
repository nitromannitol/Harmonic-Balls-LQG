import HarmonicBalls.Defs.Annuli
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Finite covers of annuli

A finite covering of the middle annulus by discs compactly contained in a
larger annulus is the geometric input to the mass estimate of Lemma 6.8.
-/

namespace HarmonicBalls.Section6

open Set Metric

/-- A middle annulus has a finite disc cover whose doubled closed discs lie in
the outer annulus. The radius and centres depend only on the four radii. -/
theorem exists_finite_middle_annulus_cover {s₁ s₂ s₃ s₄ : ℝ}
    (h12 : s₁ < s₂) (h34 : s₃ < s₄) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ T : Set ℂ, T.Finite ∧
      T ⊆ annulus 0 s₂ s₃ ∧
      annulus 0 s₂ s₃ ⊆ ⋃ x ∈ T, ball x δ ∧
      ∀ x ∈ T, closedBall x (2 * δ) ⊆ annulus 0 s₁ s₄ := by
  let δ : ℝ := min (s₂ - s₁) (s₄ - s₃) / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : 2 * δ < s₂ - s₁ := by dsimp [δ]; have := min_le_left (s₂ - s₁) (s₄ - s₃); linarith
  have hδ2 : 2 * δ < s₄ - s₃ := by dsimp [δ]; have := min_le_right (s₂ - s₁) (s₄ - s₃); linarith
  have hb : Bornology.IsBounded (annulus (0 : ℂ) s₂ s₃) := isBounded_ball.subset sdiff_subset
  obtain ⟨T, hTsub, hTfin, hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hb.isCompact_closure hδ
  refine ⟨δ, hδ, T, hTfin, hTsub, hcover, ?_⟩
  intro x hx y hy
  have hx' : s₂ < dist x 0 ∧ dist x 0 < s₃ := by
    simpa only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le, and_comm] using hTsub hx
  have hy' : dist y x ≤ 2 * δ := mem_closedBall.mp hy
  have hupper := dist_triangle y x 0
  have hlower := dist_triangle x y 0
  have hsymm : dist x y = dist y x := dist_comm x y
  change y ∈ ball 0 s₄ ∧ y ∉ closedBall 0 s₁
  simp only [mem_ball, mem_closedBall, not_le]
  constructor <;> linarith

end HarmonicBalls.Section6
