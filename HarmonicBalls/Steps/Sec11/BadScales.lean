import HarmonicBalls.Draft.Section11

/-! # Positive density implies arbitrarily small bad scales -/

namespace HarmonicBalls

open Set Filter

/-- The positive lower density in the dyadic blocks of Lemmas 11.7 and 11.13
implies that the event occurs at arbitrarily large indices. -/
theorem frequently_of_positive_dyadic_block_density (E : ℕ → Prop) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ᶠ N : ℕ in atTop,
      δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n}.ncard : ℝ)) :
    ∃ᶠ n in atTop, E n := by
  rw [Filter.frequently_atTop]
  intro k
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  let N := max N₀ (max k 1)
  have hNN₀ : N₀ ≤ N := le_max_left _ _
  have hk : k ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 1)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  have hcount := hN₀ N hNN₀
  have hne : ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n} : Set ℕ).Nonempty := by
    by_contra hempty
    have heq : ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n} : Set ℕ) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    rw [heq, Set.ncard_empty, Nat.cast_zero] at hcount
    have : (0 : ℝ) < δ * N := mul_pos hδ (by exact_mod_cast hNpos)
    linarith
  obtain ⟨n, hn₁, hn₂, hnE⟩ := hne
  exact ⟨n, by omega, hnE⟩

end HarmonicBalls
