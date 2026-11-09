import HarmonicBalls.FirstPass.S11c.Frequency
import HarmonicBalls.FirstPass.S11c.Window

/-!
# Proposition 11.7, the window count of an ergodic event (fp-S11c, owner n1)

FIRST-PASS NEW (composition of two compiled steps). Let `T` be ergodic and measure-preserving on a probability space, and
let `E` be a measurable event of probability at least `p > 0`. Then almost surely the number of visits of the orbit to `E`
in the window `[N+1, 2N]` is at least `(p/4) N` for all large `N`. This is the abstract form of the window bound of the
paper's proof of `lemma:mu_h-bad-and-harnack` (Lemma 11.7): the scale events at the origin are visits of an ergodic
dilation, and `P(E) ≥ p` is the positive-probability lower bound of Lemma 11.8 at `z = 0`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Finset

open Classical in
theorem ae_window_count_of_ergodic {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Ω → Ω} (herg : Ergodic T P) {E : Set Ω} (hE : MeasurableSet E) {p : ℝ} (hp : 0 < p)
    (hpE : p ≤ (P E).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      p / 4 * (N : ℝ) ≤ (((Finset.Icc (N + 1) (2 * N)).filter (fun n => T^[n] ω ∈ E)).card : ℝ) := by
  filter_upwards [ae_visit_frequency_tendsto P herg hE] with ω hω
  have hq : 0 < (P E).toReal := lt_of_lt_of_le hp hpE
  have hw := window_count_of_frequency (b := fun n => T^[n] ω ∈ E) hq hω
  filter_upwards [hw] with N hN
  have : p / 4 * (N : ℝ) ≤ (P E).toReal / 4 * (N : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

end HarmonicBalls
