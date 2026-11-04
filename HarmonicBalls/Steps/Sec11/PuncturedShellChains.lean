import HarmonicBalls.Steps.Sec11.PunctureCrossing

/-! # Summable chains of punctured shells

Overlapping shells with summable internal diameters give uniformly small
punctured internal distances near the origin.
-/

namespace HarmonicBalls

open Set Filter Topology
open scoped ENNReal NNReal

/-- The internal distance along an overlapping chain is bounded by the sum
of the internal diameter bounds of the traversed pieces. -/
theorem IsEuclideanLengthMetric.internalMetric_le_sum_shell_chain
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (U : Set ℂ)
    (A : ℕ → Set ℂ) (z : ℕ → ℂ) (c : ℕ → ℝ≥0∞)
    (hz : ∀ n, z (n + 1) ∈ A n ∧ z (n + 1) ∈ A (n + 1))
    (hdiam : ∀ n, ∀ x ∈ A n, ∀ y ∈ A n, internalMetric D U x y ≤ c n)
    (n k : ℕ) {x y : ℂ} (hx : x ∈ A n) (hy : y ∈ A (n + k)) :
    internalMetric D U x y ≤ ∑ i ∈ Finset.range (k + 1), c (n + i) := by
  induction k generalizing y with
  | zero =>
    simpa only [Nat.zero_add, Nat.add_zero, Finset.range_one, Finset.sum_singleton] using
      hdiam n x hx y hy
  | succ k ih =>
    have hanchor := hz (n + k)
    have hprev : z (n + k + 1) ∈ A (n + k) := hanchor.1
    have hnext : z (n + k + 1) ∈ A (n + (k + 1)) := by
      simpa only [Nat.add_assoc] using hanchor.2
    rw [Finset.sum_range_succ]
    calc
      internalMetric D U x y ≤ internalMetric D U x (z (n + k + 1)) +
          internalMetric D U (z (n + k + 1)) y := hD.internalMetric_triangle U _ _ _
      _ ≤ (∑ i ∈ Finset.range (k + 1), c (n + i)) + c (n + (k + 1)) :=
        add_le_add (ih hprev) (hdiam _ _ hnext y hy)

/-- A finite block of a nonnegative series is bounded by any earlier tail. -/
theorem sum_shell_chain_le_tsum_tail (c : ℕ → ℝ≥0∞) {N n k : ℕ} (hN : N ≤ n) :
    (∑ i ∈ Finset.range (k + 1), c (n + i)) ≤ ∑' i, c (i + N) := by
  calc
    (∑ i ∈ Finset.range (k + 1), c (n + i)) ≤ ∑' i, c (i + n) := by
      simpa only [Nat.add_comm] using ENNReal.sum_le_tsum (f := fun i => c (i + n))
        (Finset.range (k + 1))
    _ ≤ ∑' i, c (i + N) := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
      have h := ENNReal.tsum_comp_le_tsum_of_injective
        (show Function.Injective (fun i : ℕ => i + d) from fun _ _ h => Nat.add_right_cancel h)
        (fun i => c (i + N))
      simpa only [Function.comp_apply, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- If punctured neighborhoods are covered by arbitrarily late shells whose
internal diameters form a finite series, their punctured internal diameters
vanish near the origin. -/
theorem IsEuclideanLengthMetric.small_detours_of_summable_shells
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (V : Set ℂ)
    (A : ℕ → Set ℂ) (z : ℕ → ℂ) (c : ℕ → ℝ≥0∞)
    (hz : ∀ n, z (n + 1) ∈ A n ∧ z (n + 1) ∈ A (n + 1))
    (hdiam : ∀ n, ∀ x ∈ A n, ∀ y ∈ A n,
      internalMetric D (V \ {0}) x y ≤ c n)
    (hsum : (∑' n, c n) ≠ ∞)
    (hcover : ∀ N, ∃ r : ℝ, 0 < r ∧ ∀ a ∈ V, a ≠ 0 → ‖a‖ < r →
      ∃ n, N ≤ n ∧ a ∈ A n) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ r : ℝ, 0 < r ∧
      ∀ a b : ℂ, a ∈ V → b ∈ V → a ≠ 0 → b ≠ 0 → ‖a‖ < r → ‖b‖ < r →
        internalMetric D (V \ {0}) a b < ε := by
  intro ε hε
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have htend := ENNReal.tendsto_sum_nat_add c hsum
  have htail : ∀ᶠ N in atTop, (∑' i, c (i + N)) < ε := htend.eventually_lt_const hε'
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htail
  obtain ⟨r, hr, hcov⟩ := hcover N
  refine ⟨r, hr, ?_⟩
  intro a b ha hb ha0 hb0 har hbr
  obtain ⟨n, hn, han⟩ := hcov a ha ha0 har
  obtain ⟨m, hm, hbm⟩ := hcov b hb hb0 hbr
  have hNtail := hN N le_rfl
  rcases le_total n m with hnm | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact ((hD.internalMetric_le_sum_shell_chain (V \ {0}) A z c hz hdiam n k han hbm).trans
      (sum_shell_chain_le_tsum_tail c hn)).trans_lt hNtail
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [hD.internalMetric_symm (V \ {0}) a b]
    exact ((hD.internalMetric_le_sum_shell_chain (V \ {0}) A z c hz hdiam m k hbm han).trans
      (sum_shell_chain_le_tsum_tail c hm)).trans_lt hNtail

/-- Summable overlapping punctured shells permit removal of the origin from
the domain of the internal metric for nonzero endpoints. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_summable_shells
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (V : Set ℂ)
    (A : ℕ → Set ℂ) (z : ℕ → ℂ) (c : ℕ → ℝ≥0∞)
    (hz : ∀ n, z (n + 1) ∈ A n ∧ z (n + 1) ∈ A (n + 1))
    (hdiam : ∀ n, ∀ x ∈ A n, ∀ y ∈ A n,
      internalMetric D (V \ {0}) x y ≤ c n)
    (hsum : (∑' n, c n) ≠ ∞)
    (hcover : ∀ N, ∃ r : ℝ, 0 < r ∧ ∀ a ∈ V, a ≠ 0 → ‖a‖ < r →
      ∃ n, N ≤ n ∧ a ∈ A n)
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric D (V \ {0}) x y = internalMetric D V x y :=
  hD.internalMetric_sdiff_zero_eq_of_small_detours hx hy
    (hD.small_detours_of_summable_shells V A z c hz hdiam hsum hcover)

#print axioms IsEuclideanLengthMetric.internalMetric_le_sum_shell_chain
#print axioms sum_shell_chain_le_tsum_tail
#print axioms IsEuclideanLengthMetric.small_detours_of_summable_shells
#print axioms IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_summable_shells

end HarmonicBalls
