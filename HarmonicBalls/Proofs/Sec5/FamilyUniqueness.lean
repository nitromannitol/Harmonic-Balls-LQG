import HarmonicBalls.Draft.Section5

/-!
# Uniqueness of the regularized cluster family

The compatibility clause in Theorem 5.5 uniquely determines the family:
at a fixed positive time, choose a ball containing both closures and apply
the clause to the same ambient radius.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Two families satisfying Theorem 5.5 agree at every positive time. -/
theorem IsRegularizedClusterFamily.eqOn {μ : Measure ℂ} {Λ₁ Λ₂ : ℝ → Set ℂ} {z : ℂ}
    (h₁ : IsRegularizedClusterFamily μ Λ₁ z) (h₂ : IsRegularizedClusterFamily μ Λ₂ z) :
    EqOn Λ₁ Λ₂ (Ioi 0) := by
  intro t ht
  obtain ⟨r₁, hr₁⟩ := ((h₁.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  obtain ⟨r₂, hr₂⟩ := ((h₂.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let r := max 1 (max r₁ r₂) + 1
  have hr : 0 < r := by
    have := le_max_left (1 : ℝ) (max r₁ r₂)
    dsimp [r]
    linarith
  have hr₁r : r₁ ≤ r := by
    have h := (le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]
    linarith
  have hr₂r : r₂ ≤ r := by
    have h := (le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]
    linarith
  rw [h₁.2.2 t ht r hr (hr₁.trans (ball_subset_ball hr₁r)) r le_rfl,
    h₂.2.2 t ht r hr (hr₂.trans (ball_subset_ball hr₂r)) r le_rfl]

end HarmonicBalls
