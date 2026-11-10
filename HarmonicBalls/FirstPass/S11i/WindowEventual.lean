import Mathlib

/-!
# Window counts of eventually equal predicates (fp-S11i-11-13d, owner n3)

For predicates `P Q : ℕ → Prop` that agree from `n₀` on, the window counts `#{n : N+1 ≤ n ≤ 2N, P n}` and
`#{n : N+1 ≤ n ≤ 2N, Q n}` differ by at most `n₀`. Hence the window frequencies `#/N` of `P` and `Q` have the same limit.
This is the deterministic step that transfers a window frequency from one certificate sequence to another after finitely
many scales (the cutoff `exists_cutoff_of_closure_subset`, `FirstPass/S11ah/Cutoff.lean:53`, gives the eventual equality
used in Step 8 of `lemma:mu_h-pinch-bad`, corrected paper lines 3848-3930). No probability and no LQG input.
-/

namespace HarmonicBalls.FirstPassS11iWindowEventual

open Set Filter Topology

/-- One-sided bound: the window count of `P` is at most the window count of `Q` plus `n₀`, when `P n ↔ Q n` for `n ≥ n₀`. -/
lemma ncard_window_le_add_of_eventually (P Q : ℕ → Prop) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → (P n ↔ Q n)) (N : ℕ) :
    ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℕ) ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard : ℕ) + n₀ := by
  have hfinB : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.Finite :=
    (Set.finite_Icc (N + 1) (2 * N)).subset (fun n hn => ⟨hn.1, hn.2.1⟩)
  have hsub : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n} ⊆
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n} ∪ ((Finset.range n₀ : Finset ℕ) : Set ℕ) := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hn
    by_cases hn0 : n < n₀
    · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_range.mpr hn0))
    · exact Or.inl ⟨h1, h2, (h n (by omega)).mp h3⟩
  calc {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard
      ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n} ∪ ((Finset.range n₀ : Finset ℕ) : Set ℕ)).ncard :=
        Set.ncard_le_ncard hsub (hfinB.union (Finset.finite_toSet _))
    _ ≤ {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard + ((Finset.range n₀ : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_union_le _ _
    _ = {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard + n₀ := by
        rw [Set.ncard_coe_finset, Finset.card_range]

/-- Two window counts of predicates agreeing from `n₀` on differ by at most `n₀`. -/
lemma abs_ncard_window_sub_le (P Q : ℕ → Prop) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → (P n ↔ Q n)) (N : ℕ) :
    |(({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℕ) : ℝ) -
        (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard : ℕ) : ℝ)| ≤ (n₀ : ℝ) := by
  have h1 := ncard_window_le_add_of_eventually P Q n₀ h N
  have h2 := ncard_window_le_add_of_eventually Q P n₀ (fun n hn => (h n hn).symm) N
  rw [abs_le]
  constructor
  · have : (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard : ℕ) : ℝ) ≤
        (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℕ) : ℝ) + (n₀ : ℝ) := by
      exact_mod_cast h2
    linarith
  · have : (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℕ) : ℝ) ≤
        (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard : ℕ) : ℝ) + (n₀ : ℝ) := by
      exact_mod_cast h1
    linarith

/-- **Window frequencies of eventually equal predicates have the same limit.** If the window frequency `#/N` of `P` tends
to `q`, so does that of `Q`, when `P n ↔ Q n` for all `n ≥ n₀`. -/
theorem tendsto_window_freq_of_eventually (P Q : ℕ → Prop) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → (P n ↔ Q n)) {q : ℝ}
    (hP : Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 q)) :
    Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 q) := by
  have hbound : ∀ N : ℕ,
      ‖(({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard : ℕ) : ℝ) / (N : ℝ) -
          (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℕ) : ℝ) / (N : ℝ)‖ ≤
        (n₀ : ℝ) / (N : ℝ) := by
    intro N
    rw [← sub_div, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have := abs_ncard_window_sub_le P Q n₀ h N
    rw [abs_sub_comm]
    exact this
  have hdiff : Tendsto (fun N : ℕ => (n₀ : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hsqz := squeeze_zero_norm hbound hdiff
  have hsum := hP.add hsqz
  rw [add_zero] at hsum
  exact hsum.congr (fun N => by ring)

end HarmonicBalls.FirstPassS11iWindowEventual
