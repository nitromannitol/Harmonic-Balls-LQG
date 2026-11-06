import HarmonicBalls.Proofs.Sec6.VeryGoodThresholdMonotonicity

/-! # Criterion three on the interior of a nearby root annulus

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

/-- Criterion three at a grid centre also applies to points in the root-centred
annulus after removing a collar of width equal to the displacement. The lattice
is the same absolute lattice at both centres. -/
theorem veryGoodAnnulus_criterionThree_nearby_interior
    {μ : Measure ℂ} {β ρ a b C₁m C₁p C₂m C₂p C₃ : ℝ}
    {z w x : ℂ} {N₀ n : ℕ}
    (h : IsVeryGoodAnnulus μ β ρ z N₀ a b C₁m C₁p C₂m C₂p C₃)
    (hn : N₀ ≤ n)
    (hxlo : ρ / 2 + dist w z < dist x w)
    (hxhi : dist x w < ρ - dist w z)
    (hlat : ∃ j k : ℤ, x = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) *
      ((j : ℂ) + (k : ℂ) * Complex.I)) :
    C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ r x a b}.ncard : ℝ) := by
  apply h.2.2 n hn x _ hlat
  simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le]
  constructor
  · have ht := dist_triangle x w z
    linarith
  · have ht := dist_triangle x z w
    rw [dist_comm z w] at ht
    linarith

end HarmonicBalls.Section6
