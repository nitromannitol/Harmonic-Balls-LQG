import HarmonicBalls.Steps.Sec11.PuncturedShellChains

/-! # Geometric annuli around the origin

Geometric annuli overlap and cover every sufficiently small punctured
neighborhood. Their summable internal diameter bounds imply point removal.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- The closed annulus between successive scales of a geometric sequence. -/
def geometricShell (R q : ℝ) (n : ℕ) : Set ℂ :=
  {x | R * q ^ (n + 1) ≤ ‖x‖ ∧ ‖x‖ ≤ R * q ^ n}

/-- Every sufficiently small nonzero point lies in a geometric shell of
arbitrarily late index. -/
theorem geometricShell_covers_tail {R q : ℝ} (hR : 0 < R) (hq : 0 < q) (hq1 : q < 1)
    (N : ℕ) : ∃ r : ℝ, 0 < r ∧ ∀ a : ℂ, a ≠ 0 → ‖a‖ < r →
      ∃ n, N ≤ n ∧ a ∈ geometricShell R q n := by
  let r := R * q ^ N
  have hr : 0 < r := mul_pos hR (pow_pos hq _)
  refine ⟨r, hr, ?_⟩
  intro a ha har
  have hx : 0 < ‖a‖ / r := div_pos (norm_pos_iff.mpr ha) hr
  have hx1 : ‖a‖ / r ≤ 1 := (div_le_one hr).2 har.le
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hx hx1 hq hq1
  refine ⟨N + k, Nat.le_add_right N k, ?_⟩
  have hlo : r * q ^ (k + 1) < ‖a‖ := by
    simpa only [mul_comm] using (lt_div_iff₀ hr).mp hk1
  have hhi : ‖a‖ ≤ r * q ^ k := by
    simpa only [mul_comm] using (div_le_iff₀ hr).mp hk2
  constructor
  · simpa only [geometricShell, mem_ofPred_eq, pow_add, ← mul_assoc, r] using hlo.le
  · simpa only [geometricShell, mem_ofPred_eq, pow_add, ← mul_assoc, r] using hhi

/-- Adjacent geometric annuli meet at the corresponding positive real point. -/
theorem geometricShell_bridge {R q : ℝ} (hR : 0 < R) (hq : 0 < q) (hq1 : q < 1)
    (n : ℕ) :
    ((R * q ^ (n + 1) : ℝ) : ℂ) ∈ geometricShell R q n ∧
    ((R * q ^ (n + 1) : ℝ) : ℂ) ∈ geometricShell R q (n + 1) := by
  have hpos : 0 ≤ R * q ^ (n + 1) := (mul_pos hR (pow_pos hq _)).le
  have hp : q ^ (n + 1) ≤ q ^ n := by
    rw [pow_succ]
    nlinarith [pow_nonneg hq.le n]
  have hn : q ^ (n + 1 + 1) ≤ q ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg hq.le (n + 1)]
  simp only [geometricShell, mem_ofPred_eq, Complex.norm_real, Real.norm_of_nonneg hpos]
  exact ⟨⟨le_rfl, mul_le_mul_of_nonneg_left hp hR.le⟩,
    ⟨mul_le_mul_of_nonneg_left hn hR.le, le_rfl⟩⟩

/-- Summable punctured internal diameters of geometric annuli imply that
removing the origin preserves internal distances between nonzero points. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_geometric_shells
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (V : Set ℂ)
    {R q : ℝ} (hR : 0 < R) (hq : 0 < q) (hq1 : q < 1)
    (c : ℕ → ℝ≥0∞)
    (hdiam : ∀ n, ∀ x ∈ geometricShell R q n, ∀ y ∈ geometricShell R q n,
      internalMetric D (V \ {0}) x y ≤ c n)
    (hsum : (∑' n, c n) ≠ ∞) {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric D (V \ {0}) x y = internalMetric D V x y := by
  apply hD.internalMetric_sdiff_zero_eq_of_summable_shells V (geometricShell R q)
    (fun n => ((R * q ^ n : ℝ) : ℂ)) c (geometricShell_bridge hR hq hq1) hdiam hsum
  · intro N
    obtain ⟨r, hr, hcover⟩ := geometricShell_covers_tail hR hq hq1 N
    exact ⟨r, hr, fun a _ ha har => hcover a ha har⟩
  · exact hx
  · exact hy

#print axioms geometricShell_covers_tail
#print axioms geometricShell_bridge
#print axioms IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_geometric_shells

end HarmonicBalls
