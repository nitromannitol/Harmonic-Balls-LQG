import Mathlib

/-! # Finite shifts of dyadic index windows

The rooted argument in Section 11 transfers a positive block density across
a fixed dyadic change of scale. These estimates isolate its finite counting
step; no independence or stationarity is involved.
-/

open Finset
open Filter

namespace HarmonicBalls

/-- A fixed shift changes either end of the dyadic index window by at most
`k` indices. -/
theorem pinch_window_sdiff_card_le (N k : ℕ) :
    ((Icc (N + 1) (2 * N)) \ (Icc (N + k + 1) (2 * N + k))).card ≤ k ∧
    ((Icc (N + k + 1) (2 * N + k)) \ (Icc (N + 1) (2 * N))).card ≤ k := by
  constructor
  · calc
      _ ≤ (Icc (N + 1) (N + k)).card := by
        apply card_le_card
        intro x hx
        simp only [Finset.mem_sdiff, mem_Icc, not_and_or, not_le] at hx ⊢
        omega
      _ = k := by simp [Nat.card_Icc]
  · calc
      _ ≤ (Icc (2 * N + 1) (2 * N + k)).card := by
        apply card_le_card
        intro x hx
        simp only [Finset.mem_sdiff, mem_Icc, not_and_or, not_le] at hx ⊢
        omega
      _ = k := by simp [Nat.card_Icc]

/-- Counts of any fixed set of indices in the two windows differ by at most
`k` in each direction. -/
theorem pinch_window_filter_card_le (S : Set ℕ) [DecidablePred (· ∈ S)] (N k : ℕ) :
    ((Icc (N + 1) (2 * N)).filter (· ∈ S)).card ≤
        ((Icc (N + k + 1) (2 * N + k)).filter (· ∈ S)).card + k ∧
    ((Icc (N + k + 1) (2 * N + k)).filter (· ∈ S)).card ≤
        ((Icc (N + 1) (2 * N)).filter (· ∈ S)).card + k := by
  have h := pinch_window_sdiff_card_le N k
  let a := Icc (N + 1) (2 * N)
  let b := Icc (N + k + 1) (2 * N + k)
  have aux (a b : Finset ℕ) : (a.filter (· ∈ S) \ b.filter (· ∈ S)) ⊆ a \ b := by
    intro x hx
    simp only [Finset.mem_sdiff, mem_filter] at hx ⊢
    exact ⟨hx.1.1, fun hmem => hx.2 ⟨hmem, hx.1.2⟩⟩
  have h₁ : ((a.filter (· ∈ S)) \ (b.filter (· ∈ S))).card ≤ k :=
    (card_le_card (aux a b)).trans h.1
  have h₂ : ((b.filter (· ∈ S)) \ (a.filter (· ∈ S))).card ≤ k :=
    (card_le_card (aux b a)).trans h.2
  have h₃ := card_le_card_sdiff_add_card (s := a.filter (· ∈ S)) (t := b.filter (· ∈ S))
  have h₄ := card_le_card_sdiff_add_card (s := b.filter (· ∈ S)) (t := a.filter (· ∈ S))
  change (a.filter (· ∈ S)).card ≤ (b.filter (· ∈ S)).card + k ∧
    (b.filter (· ∈ S)).card ≤ (a.filter (· ∈ S)).card + k
  constructor <;> omega

/-- A fixed shift of the dyadic window preserves any strictly smaller
asymptotic block-density lower bound. -/
theorem eventually_pinch_window_shift_density
    (S : Set ℕ) [DecidablePred (· ∈ S)] (k : ℕ) {q q' : ℝ} (hqq : q' < q)
    (h : ∀ᶠ N : ℕ in atTop,
      q * N ≤ (((Icc (N + 1) (2 * N)).filter (· ∈ S)).card : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      q' * N ≤ (((Icc (N + k + 1) (2 * N + k)).filter (· ∈ S)).card : ℝ) := by
  have ht : Tendsto (fun N : ℕ => (q - q') * (N : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop' (sub_pos.mpr hqq) tendsto_natCast_atTop_atTop
  have hk : ∀ᶠ N : ℕ in atTop, (k : ℝ) ≤ (q - q') * N :=
    ht.eventually (eventually_ge_atTop (k : ℝ))
  filter_upwards [h, hk] with N hN hkN
  have hc := (pinch_window_filter_card_le S N k).1
  have hc' : (((Icc (N + 1) (2 * N)).filter (· ∈ S)).card : ℝ) ≤
      (((Icc (N + k + 1) (2 * N + k)).filter (· ∈ S)).card : ℝ) + k := by
    exact_mod_cast hc
  nlinarith

end HarmonicBalls
