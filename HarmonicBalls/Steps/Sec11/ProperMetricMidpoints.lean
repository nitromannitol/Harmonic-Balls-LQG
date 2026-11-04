import HarmonicBalls.Steps.Sec11.ApproximatePaths
import HarmonicBalls.Steps.Sec11.PinchInequalities

/-!
# Midpoints in proper length metrics

Compactness of closed metric balls yields exact midpoints from nearly
minimizing paths. This is a step toward the geodesic existence theorem for a
proper length space.
-/

namespace HarmonicBalls

open Metric Set
open scoped ENNReal

/-- A length metric has points at half the distance from one endpoint, whose
remaining distance is arbitrarily close to half the endpoint distance. -/
theorem IsEuclideanLengthMetric.exists_approximate_midpoint
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (x y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℂ, D x m = D x y / 2 ∧ D m y < D x y / 2 + ε := by
  obtain ⟨p, hp⟩ := hD.exists_pathLength_lt hnonneg x y hε
  have hc : Continuous fun t : ℝ => D x (p.extend t) := by
    have h : Continuous fun m : ℂ => D x m := by
      simpa only [hD.symm x] using hD.continuous_left x
    exact h.comp p.continuous_extend
  have hmem : D x y / 2 ∈ Icc (D x (p.extend 0)) (D x (p.extend 1)) := by
    simp only [p.extend_zero, p.extend_one, hD.self_eq_zero]
    constructor <;> linarith [hnonneg x y]
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (zero_le_one' ℝ) hc.continuousOn hmem
  have hsum := lt_of_le_of_lt (hD.ofReal_two_segment_le_pathLength hnonneg p ht) hp
  have hreal : D x (p.extend t) + D (p.extend t) y < D x y + ε :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (add_nonneg (hnonneg x (p.extend t)) (hnonneg (p.extend t) y))).1 hsum
  exact ⟨p.extend t, heq, by linarith⟩

/-- A Euclidean length metric whose closed metric balls are compact has exact
midpoints. Compactness is an explicit hypothesis. -/
theorem IsEuclideanLengthMetric.exists_midpoint_of_compact_closedBalls
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hcompact : ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D x z ≤ R})
    (x y : ℂ) : ∃ m : ℂ, D x m = D x y / 2 ∧ D m y = D x y / 2 := by
  let S : Set ℂ := {m | D x m = D x y / 2}
  have hc : Continuous fun m : ℂ => D x m := by
    simpa only [hD.symm x] using hD.continuous_left x
  have hclosed : IsClosed S := isClosed_eq hc continuous_const
  have hScompact : IsCompact S := (hcompact x (D x y / 2)).of_isClosed_subset hclosed (by
    intro m hm
    exact le_of_eq hm)
  obtain ⟨m₀, hm₀, _⟩ := hD.exists_approximate_midpoint hnonneg x y zero_lt_one
  have hSnonempty : S.Nonempty := ⟨m₀, hm₀⟩
  obtain ⟨m, hm, hmin⟩ := hScompact.exists_isMinOn hSnonempty
    (hD.continuous_left y).continuousOn
  have hupper : D m y ≤ D x y / 2 := by
    by_contra hn
    have heps : 0 < (D m y - D x y / 2) / 2 := by linarith
    obtain ⟨m', hm', hnear⟩ := hD.exists_approximate_midpoint hnonneg x y heps
    have hle : D m y ≤ D m' y := hmin hm'
    linarith
  have htri := hD.triangle x m y
  have hlower : D x y / 2 ≤ D m y := by
    change D x m = D x y / 2 at hm
    linarith
  exact ⟨m, hm, le_antisymm hupper hlower⟩

end HarmonicBalls
