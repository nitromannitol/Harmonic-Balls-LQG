import Mathlib

/-!
# From a positive frequency of good scales to window counts (Lemma 11.7, counting step)

NEW step of Lemma 11.7 (lemma:mu_h-bad-and-harnack, paper line 2802). The printed proof (lines 2911-2951) passes from a
positive limiting frequency `q` of good scales (given by the pointwise ergodic theorem) to the count
`#{n ∈ [N+1, 2N] : G̃_n(z) occurs} ≥ δ N` with `δ = q/2`. This module proves that deterministic counting step:
if the Cesàro frequency of a `ℕ`-indexed predicate tends to `q > 0`, then the number of its occurrences in the window
`(N, 2N]` is eventually at least `q N / 2`.
-/

open Filter Topology Finset

namespace HarmonicBalls

namespace FirstPassS11

/-- The number of occurrences of `b` among the first `N` positive integers. -/
noncomputable def occCount (b : ℕ → Prop) [DecidablePred b] (N : ℕ) : ℕ :=
  ((Ioc 0 N).filter b).card

/-- The window `(N, 2N]` count is the difference of the initial counts. -/
lemma window_card_eq (b : ℕ → Prop) [DecidablePred b] (N : ℕ) :
    (((Icc (N + 1) (2 * N)).filter b).card : ℤ) = (occCount b (2 * N) : ℤ) - (occCount b N : ℤ) := by
  have hsplit : (Ioc 0 (2 * N)).filter b =
      (Ioc 0 N).filter b ∪ (Ioc N (2 * N)).filter b := by
    ext n
    simp only [mem_filter, mem_union, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hb⟩
      by_cases hn : n ≤ N
      · exact Or.inl ⟨⟨h1, hn⟩, hb⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, hb⟩
    · rintro (⟨⟨h1, h2⟩, hb⟩ | ⟨⟨h1, h2⟩, hb⟩)
      · exact ⟨⟨h1, by omega⟩, hb⟩
      · exact ⟨⟨by omega, h2⟩, hb⟩
  have hdisj : Disjoint ((Ioc 0 N).filter b) ((Ioc N (2 * N)).filter b) := by
    refine Finset.disjoint_left.2 fun n hn hn' => ?_
    simp only [mem_filter, mem_Ioc] at hn hn'
    omega
  have hwin : (Icc (N + 1) (2 * N)).filter b = (Ioc N (2 * N)).filter b := by
    ext n
    simp only [mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hb⟩; exact ⟨⟨by omega, h2⟩, hb⟩
    · rintro ⟨⟨h1, h2⟩, hb⟩; exact ⟨⟨by omega, h2⟩, hb⟩
  unfold occCount
  rw [hwin, hsplit, Finset.card_union_of_disjoint hdisj]
  push_cast
  ring

/-- Counting step of Lemma 11.7: a positive Cesàro frequency `q` of the predicate `b` gives, eventually,
at least `q N / 2` occurrences of `b` in the window `(N, 2N]`. -/
theorem eventually_window_count_ge (b : ℕ → Prop) [DecidablePred b] {q : ℝ} (hq : 0 < q)
    (hfreq : Tendsto (fun N : ℕ => (occCount b N : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    ∀ᶠ N : ℕ in atTop, q / 2 * (N : ℝ) ≤ (((Icc (N + 1) (2 * N)).filter b).card : ℝ) := by
  -- the doubled frequency tends to `2 q`
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_atTop.2 fun m => ⟨m, fun n hn => by omega⟩
  have hdouble : Tendsto (fun N : ℕ => (occCount b (2 * N) : ℝ) / ((2 * N : ℕ) : ℝ)) atTop (𝓝 q) :=
    hfreq.comp h2N
  have hratio : Tendsto (fun N : ℕ => (occCount b (2 * N) : ℝ) / (N : ℝ)) atTop (𝓝 (2 * q)) := by
    have h2 := hdouble.const_mul 2
    refine h2.congr' ?_
    filter_upwards with N
    push_cast
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have hN : (N : ℝ) ≠ 0 := by exact_mod_cast h.ne'
      field_simp
  -- difference of the two frequencies, normalised by `N`
  have hdiff : Tendsto (fun N : ℕ => (occCount b (2 * N) : ℝ) / (N : ℝ) - (occCount b N : ℝ) / (N : ℝ))
      atTop (𝓝 (2 * q - q)) := hratio.sub hfreq
  have hlim : 2 * q - q = q := by ring
  rw [hlim] at hdiff
  have hev := hdiff.eventually (lt_mem_nhds (by linarith : q / 2 < q))
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hpos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hpos
  have hcard := window_card_eq b N
  have hcast : (((Icc (N + 1) (2 * N)).filter b).card : ℝ) =
      (occCount b (2 * N) : ℝ) - (occCount b N : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hcard
    push_cast at this
    exact this
  rw [hcast]
  have key : q / 2 * (N : ℝ) ≤ ((occCount b (2 * N) : ℝ) - (occCount b N : ℝ)) := by
    have h' : q / 2 < (occCount b (2 * N) : ℝ) / (N : ℝ) - (occCount b N : ℝ) / (N : ℝ) := hN
    rw [← sub_div, lt_div_iff₀ hNpos] at h'
    nlinarith [h']
  exact key

end FirstPassS11

end HarmonicBalls
