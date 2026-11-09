import Mathlib

/-!
# Index shift of a window count (Lemma 11.13, dilation step)

NEW deterministic step of Lemma 11.13 (`lemma:mu_h-pinch-bad`, corrected proof, paper lines 3900-3910, correction [C45]).
After dilation by `2^k` the scale index moves by `k`. The printed argument says that shifting the index window
`[N+1, 2N]` by a fixed integer `k` changes its count by at most `2k`. This module proves the sharper one-sided bound
used there: the count in the shifted window is at least the count in `[N+1, 2N]` minus `k`.
-/

namespace FirstPassS11i

open Finset

/-- Finset form of the window-shift bound: the number of `m ∈ [N+1, 2N]` with `P m` exceeds the number of
`n ∈ [N+1, 2N]` with `P (n + k)` by at most `k`. -/
theorem card_window_shift_le (P : ℕ → Prop) [DecidablePred P] (k N : ℕ) :
    ((Icc (N + 1) (2 * N)).filter P).card ≤
      ((Icc (N + 1) (2 * N)).filter (fun n => P (n + k))).card + k := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Icc (N + 1) (2 * N)).filter P) (fun m => N + k < m)
  have hlow : (((Icc (N + 1) (2 * N)).filter P).filter (fun m => ¬ N + k < m)).card ≤ k := by
    have hsub : ((Icc (N + 1) (2 * N)).filter P).filter (fun m => ¬ N + k < m) ⊆
        Icc (N + 1) (N + k) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      omega
    have h := Finset.card_le_card hsub
    simpa using h
  have hhigh : (((Icc (N + 1) (2 * N)).filter P).filter (fun m => N + k < m)).card ≤
      ((Icc (N + 1) (2 * N)).filter (fun n => P (n + k))).card := by
    apply Finset.card_le_card_of_injOn (fun m => m - k)
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      obtain ⟨⟨⟨h1, h2⟩, hP⟩, h3⟩ := hm
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Nat.sub_add_cancel (by omega : k ≤ m)]
      exact hP
    · intro m1 hm1 m2 hm2 h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm1 hm2
      obtain ⟨_, h3⟩ := hm1
      obtain ⟨_, h4⟩ := hm2
      have h' : m1 - k = m2 - k := h
      omega
  omega

/-- Set form of the window-shift bound, in the shape of the counts `#{n ∈ [N+1, 2N] : … }` of Lemma 11.13. -/
theorem ncard_window_shift_le (P : ℕ → Prop) (k N : ℕ) :
    ({m : ℕ | N + 1 ≤ m ∧ m ≤ 2 * N ∧ P m}.ncard : ℝ) ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P (n + k)}.ncard : ℝ) + k := by
  classical
  have e1 : {m : ℕ | N + 1 ≤ m ∧ m ≤ 2 * N ∧ P m} =
      ↑((Icc (N + 1) (2 * N)).filter P) := by
    ext m
    simp [Finset.mem_Icc, and_assoc]
  have e2 : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P (n + k)} =
      ↑((Icc (N + 1) (2 * N)).filter (fun n => P (n + k))) := by
    ext n
    simp [Finset.mem_Icc, and_assoc]
  rw [e1, e2, Set.ncard_coe_finset, Set.ncard_coe_finset]
  exact_mod_cast card_window_shift_le P k N

end FirstPassS11i
