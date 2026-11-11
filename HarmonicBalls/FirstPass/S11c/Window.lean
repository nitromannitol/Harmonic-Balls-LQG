import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Proposition 11.7, the window count from the visit frequency

If the visit frequency `#{n < N : b n} / N` tends to `q > 0`, then for all
large `N` the number of visits in the window `[N+1, 2N]` is at least `(q/4) N`. This is the counting step of the proof of
`lemma:mu_h-bad-and-harnack` (Lemma 11.7, corrected `[C39]`): the window count is `C(2N+1) - C(N+1)`, where
`C(M) = #{n < M : b n}`, and `C(M) ≈ qM` on both ends.
-/

namespace HarmonicBalls

open Filter Topology Finset

lemma card_window_split (b : ℕ → Prop) [DecidablePred b] (N : ℕ) :
    ((range (2 * N + 1)).filter b).card =
      ((range (N + 1)).filter b).card + ((Icc (N + 1) (2 * N)).filter b).card := by
  have hdec : range (2 * N + 1) = range (N + 1) ∪ Icc (N + 1) (2 * N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (range (N + 1)) (Icc (N + 1) (2 * N)) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_range, Finset.mem_Icc] at hn hn'
    omega
  rw [hdec, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]

theorem window_count_of_frequency {b : ℕ → Prop} [DecidablePred b] {q : ℝ} (hq : 0 < q)
    (hfreq : Tendsto (fun N : ℕ => (((range N).filter b).card : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    ∀ᶠ N : ℕ in atTop, q / 4 * (N : ℝ) ≤ (((Icc (N + 1) (2 * N)).filter b).card : ℝ) := by
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 hfreq (q / 8) (by linarith)
  filter_upwards [eventually_ge_atTop (N0 + 1)] with N hN
  have hA := hN0 (2 * N + 1) (by omega)
  have hB := hN0 (N + 1) (by omega)
  set C : ℕ → ℝ := fun M => (((range M).filter b).card : ℝ) with hC
  have hsplit : C (2 * N + 1) = C (N + 1) + (((Icc (N + 1) (2 * N)).filter b).card : ℝ) := by
    simp only [hC]
    rw [card_window_split b N]
    push_cast
    ring
  have hApos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hBpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  rw [Real.dist_eq, abs_lt] at hA hB
  have hA' : q - q / 8 < C (2 * N + 1) / ((2 * N + 1 : ℕ) : ℝ) := by
    simp only [hC] at hA ⊢; linarith [hA.1]
  have hB' : C (N + 1) / ((N + 1 : ℕ) : ℝ) < q + q / 8 := by
    simp only [hC] at hB ⊢; linarith [hB.2]
  rw [lt_div_iff₀ hApos] at hA'
  rw [div_lt_iff₀ hBpos] at hB'
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  push_cast at hA' hB' hApos hBpos
  have hW : (((Icc (N + 1) (2 * N)).filter b).card : ℝ) = C (2 * N + 1) - C (N + 1) := by
    linarith [hsplit]
  rw [hW]
  nlinarith [hA', hB', hN1]

end HarmonicBalls
