import HarmonicBalls.Draft.Section11
import HarmonicBalls.Draft.Section6
import HarmonicBalls.FirstPass.S11i.WindowShift
import HarmonicBalls.FirstPass.S11i.CertWindow

/-!
# Lemma 11.13 (`ManyPinchScalesStmt`, lemma:mu_h-pinch-bad): first-pass status

Status: OPEN. Module contents:

* Proved: `FirstPassS11i.card_window_shift_le` and `FirstPassS11i.ncard_window_shift_le` (`FirstPass/S11i/WindowShift.lean`).
  Index shift of the window `[N+1, 2N]` by `k` costs at most `k` (printed text: at most `2k`; corrected proof, paper
  lines 3900-3910).
* Open NEW step: `HarmonicBalls.PinchPositiveRepairedStmt` below, the positivity of the repaired Lemma 11.12 at every
  exponent `α < Q`, used at `α = γ` in the rooted transfer (corrected proof, paper lines 3877-3894). Its written argument is
  `notes/fp-gaps/G-11-12.md` sections 1-6 (referee verdict CORRECT, `notes/fp-gaps/CHATGPT-G-8-2-G-11-12.md`). It is a
  statement to be proved, not an input, and it is not frozen.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- NEW statement, open (not frozen, not assumed): repaired positivity of the pinch event at every exponent `α < lqgQ γ`.
For each `α`, `M > 0` and model `(P, hC, hcirc, μ, D)` there is an event `E` of the field σ-algebra on `B_7` modulo
additive constants with `0 < P E`, on which the pinch holds almost surely, and an ambient measurable `A ⊆ E` with
`A` contained pointwise in the raw pinch event and `P A = P E` (notes/fp-gaps/G-11-12.md section 6).

The pointwise local containment `E ⊆ {pinch}` is refuted by the flag construction of G-11-12 section 6, so it is not used. -/
def PinchPositiveRepairedStmt : Prop :=
  ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
  ∀ γ ξ α : ℝ, 0 < γ → γ < 2 → α < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
  ∀ M : ℝ, 0 < M →
    ∃ E A : Set Ω,
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball 0 7)] E ∧ 0 < P E ∧
      (∀ᵐ ω ∂P, ω ∈ E → pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0) ∧
      MeasurableSet A ∧ A ⊆ E ∧
      A ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0} ∧ P A = P E

end HarmonicBalls
