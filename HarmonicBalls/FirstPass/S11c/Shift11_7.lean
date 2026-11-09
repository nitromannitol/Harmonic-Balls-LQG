import Mathlib

/-!
# First pass, Lemma 11.7: the window shift (fp-S11c, owner n1)

Step S6 bookkeeping. `origin_window_visits` (S11c/Origin11_7.lean) counts the cone event at the scales `2^{-(N₀+n)}`,
`n ∈ [N+1, 2N]`; the Draft statement `ManyConeBadScalesStmt` counts the scales `2^{-n}`, `n ∈ [N+1, 2N]`. The two windows
differ by the translation by `N₀`, which changes a count by at most `N₀` indices.
-/

open Filter Finset

namespace HarmonicBalls.S11c

/-- The count of a shifted window is at most the count of the window `[N+1, 2N]` plus `N₀`. -/
theorem card_filter_shift_le (b : ℕ → Prop) [DecidablePred b] (N N0 : ℕ) :
    ((Finset.Icc (N + 1) (2 * N)).filter (fun n => b (N0 + n))).card ≤
      ((Finset.Icc (N + 1) (2 * N)).filter b).card + N0 := by
  have h1 : ((Finset.Icc (N + 1) (2 * N)).filter (fun n => b (N0 + n))).card ≤
      ((Finset.Icc (N + 1) (2 * N + N0)).filter b).card := by
    apply Finset.card_le_card_of_injOn (fun n => N0 + n)
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨⟨h2, h3⟩, h4⟩ := hn
      exact ⟨⟨by omega, by omega⟩, h4⟩
    · intro a _ c _ h
      simpa using h
  have h2 : (Finset.Icc (N + 1) (2 * N + N0)).filter b ⊆
      (Finset.Icc (N + 1) (2 * N)).filter b ∪ Finset.Icc (2 * N + 1) (2 * N + N0) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    by_cases h : n ≤ 2 * N
    · exact Or.inl ⟨⟨hn.1.1, h⟩, hn.2⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have h3 := Finset.card_le_card h2
  have h4 := Finset.card_union_le ((Finset.Icc (N + 1) (2 * N)).filter b)
    (Finset.Icc (2 * N + 1) (2 * N + N0))
  have h5 : (Finset.Icc (2 * N + 1) (2 * N + N0)).card = N0 := by
    rw [Nat.card_Icc]
    omega
  omega

/-- Window shift in the real-valued form: a linear lower bound on the shifted window count gives, for large `N`, a lower
bound on the unshifted window count with the additive loss `N₀`. -/
theorem window_shift_bound (b : ℕ → Prop) [DecidablePred b] {c : ℝ} (N0 : ℕ)
    (h : ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ≤ (((Finset.Icc (N + 1) (2 * N)).filter (fun n => b (N0 + n))).card : ℝ)) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) - N0 ≤ (((Finset.Icc (N + 1) (2 * N)).filter b).card : ℝ) := by
  filter_upwards [h] with N hN
  have hle := card_filter_shift_le b N N0
  have hcast : (((Finset.Icc (N + 1) (2 * N)).filter (fun n => b (N0 + n))).card : ℝ) ≤
      (((Finset.Icc (N + 1) (2 * N)).filter b).card : ℝ) + (N0 : ℝ) := by
    exact_mod_cast hle
  linarith

/-- The window bound with a positive constant `c` and the loss `N₀` absorbed: for `c > 0`, almost every-large `N` gives
`(c/2) N ≤` the unshifted window count. -/
theorem window_shift_half (b : ℕ → Prop) [DecidablePred b] {c : ℝ} (hc : 0 < c) (N0 : ℕ)
    (h : ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ≤ (((Finset.Icc (N + 1) (2 * N)).filter (fun n => b (N0 + n))).card : ℝ)) :
    ∀ᶠ N : ℕ in atTop, c / 2 * (N : ℝ) ≤ (((Finset.Icc (N + 1) (2 * N)).filter b).card : ℝ) := by
  have hbig : ∀ᶠ N : ℕ in atTop, (N0 : ℝ) ≤ c / 2 * (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ => c / 2 * (N : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by linarith) tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop (N0 : ℝ)
  filter_upwards [window_shift_bound b N0 h, hbig] with N hN hB
  linarith

end HarmonicBalls.S11c
