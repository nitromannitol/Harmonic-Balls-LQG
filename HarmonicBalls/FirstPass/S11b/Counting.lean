import HarmonicBalls.FirstPass.S11.Frequency

/-! # Counting bridge for Lemma 11.7 (fp-S11b, owner n1)

Converts the `Set.ncard` form of the counts in `ManyConeBadScalesStmt` (`Draft/Section11.lean`) into the finset
counts of `FirstPassS11.eventually_window_count_ge` (n3, `FirstPass/S11/Frequency.lean`).
-/

open Set Filter Topology

namespace HarmonicBalls

namespace FirstPassS11b

open FirstPassS11

/-- The window set `{n | N + 1 ≤ n ≤ 2N, b n}` has `ncard` equal to the card of the filtered finset. -/
lemma ncard_window_eq (b : ℕ → Prop) [DecidablePred b] (N : ℕ) :
    ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ b n}.ncard : ℝ) =
      (((Finset.Icc (N + 1) (2 * N)).filter b).card : ℝ) := by
  have hset : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ b n} = ↑((Finset.Icc (N + 1) (2 * N)).filter b) := by
    ext n
    simp [Finset.mem_Icc, and_assoc]
  rw [hset, Set.ncard_coe_finset]

/-- The initial-segment set `{n | 0 < n ≤ N, b n}` has `ncard` equal to the occurrence count `occCount b N`. -/
lemma ncard_occ_eq (b : ℕ → Prop) [DecidablePred b] (N : ℕ) :
    ({n : ℕ | 0 < n ∧ n ≤ N ∧ b n}.ncard : ℝ) = (occCount b N : ℝ) := by
  have hset : {n : ℕ | 0 < n ∧ n ≤ N ∧ b n} = ↑((Finset.Ioc 0 N).filter b) := by
    ext n
    simp [Finset.mem_Ioc, and_assoc]
  rw [hset, Set.ncard_coe_finset]
  rfl

end FirstPassS11b

end HarmonicBalls
