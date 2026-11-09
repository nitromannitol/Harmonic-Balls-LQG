import HarmonicBalls.FirstPass.S11.Frequency

/-!
# The exact cardinality bound of write-up Step 7.5 (fp-S11i, owner n3)

FIRST-PASS NEW (combinatorics only). If a predicate `b` on `ℕ` has a positive limiting frequency `q` (write-up Step 7.1)
and `b n` implies `P n`, then eventually in `N` the set `{n | N+1 ≤ n ≤ 2N ∧ P n}` has at least `q/2 · N` elements.
This is the `Set.ncard` form that `firstPass_11_13_corrected` needs (`CorrectedLemma11_13Stmt`,
`HarmonicBalls/FirstPass/S11i/Faithful.lean:72`); the window count of `b` is `eventually_window_count_ge`
(`HarmonicBalls/FirstPass/S11/Frequency.lean`).
-/

namespace HarmonicBalls

open Filter Topology Finset Set

/-- Write-up Step 7.5: the window count of a predicate `P` that dominates a predicate `b` of positive frequency `q`
is eventually at least `q/2 · N`, in the `Set.ncard` form. -/
theorem eventually_ncard_window_ge_of_freq (b P : ℕ → Prop) [DecidablePred b] (hbP : ∀ n, b n → P n) {q : ℝ}
    (hq : 0 < q) (hfreq : Tendsto (fun N : ℕ => (FirstPassS11.occCount b N : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    ∀ᶠ N : ℕ in atTop, q / 2 * (N : ℝ) ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℝ) := by
  filter_upwards [FirstPassS11.eventually_window_count_ge b hq hfreq] with N hN
  have hsub : (((Finset.Icc (N + 1) (2 * N)).filter b : Finset ℕ) : Set ℕ) ⊆
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n} := by
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn ⊢
    exact ⟨hn.1.1, hn.1.2, hbP n hn.2⟩
  have hfin : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.Finite := by
    refine (Finset.Icc (N + 1) (2 * N)).finite_toSet.subset ?_
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    exact Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨hn.1, hn.2.1⟩)
  have h1 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset] at h1
  have h2 : (((Finset.Icc (N + 1) (2 * N)).filter b).card : ℝ) ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℝ) := by
    exact_mod_cast h1
  linarith

end HarmonicBalls
