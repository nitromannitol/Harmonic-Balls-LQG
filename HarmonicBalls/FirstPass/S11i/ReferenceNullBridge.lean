import HarmonicBalls.FirstPass.S11i.ReferenceNull
import HarmonicBalls.FirstPass.S11i.CertWindow

/-!
# Window-count bridge for the reference null set (fp-S11i-11-13; write-up `CHATGPT-n3-B1-B2.md` sec. 5, eq. (29) and
the one-sided implication of the corrected certificate)

Deterministic. For certificate events `cert n x` forcing the pinch events `pinch n x`, the window count of the pinch events
is at least `q/4 · N` as soon as the certificate window average converges to `q > 0`
(`CertWindow.eventually_window_of_cert_freq`). So the pinch frequency bad set (the `badSet` of `CanonicalGood`, eq. (33),
in the form `q/4`) is contained in the certificate bad set `refBadWindowSet` of `ReferenceNull`. The Campbell null of
`ae_marked_window_null` therefore transfers to the pinch bad set by monotonicity of the lower integral.
-/

namespace HarmonicBalls.ReferenceNullS11i

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The window count as a sum of indicators: `#{n in (N, 2N] : P n} = sum_{n = N+1}^{2N} 1_{P n}`. -/
theorem ncard_window_eq_sum (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℝ) =
      ∑ n ∈ Finset.Icc (N + 1) (2 * N), if P n then (1 : ℝ) else 0 := by
  have hs : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n} = ↑((Finset.Icc (N + 1) (2 * N)).filter P) := by
    ext n
    simp [Finset.mem_Icc, and_assoc]
  rw [hs, Set.ncard_coe_finset, Finset.card_filter]
  simp

/-- The certificate window average of the indicator of `cert` is the certificate count divided by `N`. -/
theorem refWindowAverage_indicator {X : Type*} (cert : ℕ → X → Prop) (N : ℕ) (x : X) :
    refWindowAverage (fun n y => ({y | cert n y}).indicator (fun _ => (1 : ℝ)) y) N x =
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ cert n x}.ncard : ℝ) / (N : ℝ) := by
  classical
  unfold refWindowAverage
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [ncard_window_eq_sum]

/-- Pinch window bound from a certificate window limit at one point (one-sided implication `cert n x → pinch n x`). -/
theorem pinchBound_of_refWindow {X : Type*} (cert pinch : ℕ → X → Prop) (himp : ∀ n x, cert n x → pinch n x)
    {q : ℝ} (hq : 0 < q) (x : X)
    (hx : Tendsto (fun N : ℕ => refWindowAverage
      (fun n y => ({y | cert n y}).indicator (fun _ => (1 : ℝ)) y) N x) atTop (𝓝 q)) :
    ∀ᶠ N : ℕ in atTop, q / 4 * (N : ℝ) ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinch n x}.ncard : ℝ) := by
  have hfreq : Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ cert n x}.ncard : ℝ) / (N : ℝ))
      atTop (𝓝 q) := by
    simpa only [refWindowAverage_indicator] using hx
  exact HarmonicBalls.CertWindow.eventually_window_of_cert_freq (fun n => pinch n x) (fun n => cert n x) 0
    (fun n h => himp n x h) hq hfreq

/-- **Pinch bad set inside the certificate bad set.** The points at which the pinch window bound `q/4 · N ≤ #pinch` fails
(the bad set of `CanonicalGood`, eq. (33), at `δ = q/4`) lie in `refBadWindowSet` of the certificate indicators. -/
theorem pinch_bad_subset_refBad {X : Type*} (cert pinch : ℕ → X → Prop)
    (himp : ∀ n x, cert n x → pinch n x) {q : ℝ} (hq : 0 < q) :
    {x : X | ¬ ∀ᶠ N : ℕ in atTop, q / 4 * (N : ℝ) ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinch n x}.ncard : ℝ)} ⊆
      refBadWindowSet (fun n y => ({y | cert n y}).indicator (fun _ => (1 : ℝ)) y) q := by
  intro x hx hT
  exact hx (pinchBound_of_refWindow cert pinch himp hq x hT)

end HarmonicBalls.ReferenceNullS11i

#print axioms HarmonicBalls.ReferenceNullS11i.pinch_bad_subset_refBad
#print axioms HarmonicBalls.ReferenceNullS11i.ncard_window_eq_sum
