import HarmonicBalls.FirstPass.S11i.WindowShift
import HarmonicBalls.FirstPass.S11.Frequency

/-!
# Shifted-window counts from a positive frequency (Lemma 11.13, dilation step)

NEW counting step of Lemma 11.13 (`lemma:mu_h-pinch-bad`, corrected proof, paper lines 3900-3910): after dilation by
`2^k` the good scales of the dilated field sit at indices `n + k`, and the window `[N+1, 2N]` is shifted by `k`. Combining
the Cesàro-frequency counting step `HarmonicBalls.FirstPassS11.eventually_window_count_ge` (Lemma 11.7 counting step,
`FirstPass/S11/Frequency.lean`) with the window-shift bound `FirstPassS11i.card_window_shift_le` gives: a positive limiting
frequency `q` of `b` yields, eventually, at least `q N / 2 - k` occurrences of `b (n + k)` in the window `(N, 2N]`.
-/

namespace FirstPassS11i

open Filter Topology

/-- A positive limiting frequency of `b` gives, eventually in `N`, at least `q N / 2 - k` indices `n ∈ (N, 2N]` with
`b (n + k)`. -/
theorem eventually_shifted_window_count_ge (b : ℕ → Prop) [DecidablePred b] (k : ℕ) {q : ℝ} (hq : 0 < q)
    (hfreq : Tendsto (fun N : ℕ => (HarmonicBalls.FirstPassS11.occCount b N : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    ∀ᶠ N : ℕ in atTop, q / 2 * (N : ℝ) - k ≤
      (((Finset.Icc (N + 1) (2 * N)).filter (fun n => b (n + k))).card : ℝ) := by
  filter_upwards [HarmonicBalls.FirstPassS11.eventually_window_count_ge b hq hfreq] with N hN
  have h := card_window_shift_le b k N
  have h' : (((Finset.Icc (N + 1) (2 * N)).filter b).card : ℝ) ≤
      (((Finset.Icc (N + 1) (2 * N)).filter (fun n => b (n + k))).card : ℝ) + k := by
    exact_mod_cast h
  linarith

end FirstPassS11i
