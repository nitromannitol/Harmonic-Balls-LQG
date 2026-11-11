import HarmonicBalls.FirstPass.S11c.WindowErgodic

/-!
# Proposition 11.7, window visits transported from the profile law

Let `F : Ω → X` be measurable with law `ν = P.map F`, and let
`T : X → X` be ergodic for `ν` (for the circle profiles, `T` is the continuous circle dilation and `ν` the law of the
measurable circle version, `IsWholePlaneGFF.ergodic_continuousCircleDilation`, `Proofs/GFF/ContinuousCircleDilationMixing.lean:172`).
If a measurable set `E` of profiles has `ν E ≥ p > 0`, then almost surely the number of visits of the dilated profile orbit
`T^[n] (F ω)` to `E` in the window `[N+1, 2N]` is at least `(p/4) N` for all large `N`. This is the step of the paper's
proof of Lemma 11.7 (paper `lemma:mu_h-bad-and-harnack`, corrected line 2896) that transports the positive frequency of good
scales from the stationary profile law to the whole-plane GFF.
-/

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal

namespace HarmonicBalls.S11c

open Classical in
/-- Window visits of the dilated profile orbit: `ν = P.map F` ergodic for `T`, `E` measurable with `p ≤ ν E`, then almost surely
`(p/4) N ≤ #{n ∈ [N+1, 2N] : T^[n] (F ω) ∈ E}` eventually. -/
theorem ae_window_visits_of_map {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Ω → X} (hF : Measurable F)
    {T : X → X} {ν : Measure X} (hν : P.map F = ν) (herg : Ergodic T ν)
    {E : Set X} (hE : MeasurableSet E) {p : ℝ} (hp : 0 < p) (hpE : p ≤ (ν E).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      p / 4 * (N : ℝ) ≤ (((Finset.Icc (N + 1) (2 * N)).filter (fun n => T^[n] (F ω) ∈ E)).card : ℝ) := by
  have : IsProbabilityMeasure ν := by
    rw [← hν]
    infer_instance
  have h1 := ae_window_count_of_ergodic ν herg hE hp hpE
  refine ae_of_ae_map hF.aemeasurable (p := fun x : X => ∀ᶠ N : ℕ in atTop,
    p / 4 * (N : ℝ) ≤ (((Finset.Icc (N + 1) (2 * N)).filter (fun n => T^[n] x ∈ E)).card : ℝ)) ?_
  rw [hν]
  exact h1

end HarmonicBalls.S11c
