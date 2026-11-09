import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric

/-!
# First-pass frozen input for Lemmas 11.15 and 11.16 (fp-S11j, owner n4)

FIRST-PASS FROZEN input (EXTERNAL; truth check pending). A `def ... : Prop`, never an axiom.

Cameron-Martin transfer for the LQG metric event of the first pinch event (paper `lemma:first-event-proof`,
corrected paper lines 3659-3696, and Step 15.4 of notes/fp-gaps/CHATGPT-11-15-17-faithful.md): the shifted
field `h + f` for a smooth compactly supported `f` vanishing on the unit circle has a law mutually absolutely
continuous with that of the whole-plane GFF `h`, and the metric of `h + f` is the Weyl scaling `e^{ξ f} D_h`.
Hence a metric event of positive probability for `h + f` has positive probability for `h`.

Source: Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2, Proposition 2.9 (printed p. 49), for the
Cameron-Martin equivalence; Weyl scaling of the LQG metric under the field shift (Dubedat-Falconet-Gwynne-Pfeffer-Sun,
arXiv:1905.00380v2, Axiom III, and Proposition 3.17 at the insertion). The same Cameron-Martin pattern as
`CameronMartinEventTransferFrozen` (FirstPass/Frozen/S11c.lean:150), specialised to a single metric event.
-/

universe u

namespace HarmonicBalls

open MeasureTheory


/-- FIRST-PASS FROZEN (EXTERNAL; FALSE AS WRITTEN, truth check 2026-11-09, `notes/fp-gaps/CHATGPT-CM-metric-truth.md`
section 1: the predicate `B` is not required to be measurable). Superseded by
`CameronMartinMetricEventTransferMeasurableFrozen` below; kept unchanged, not used by the assembly.

Cameron-Martin transfer of a metric event under a smooth shift. For `0 < γ < 2`,
`α₀ < Q_γ`, a smooth compactly supported `f` vanishing on the unit circle, and a predicate `B` on metrics: if the event
that the Weyl-shifted metric `e^{ξ f} D_h` lies in `B` has positive probability, and both events are null-measurable,
then the event that `D_h` lies in `B` has positive probability. -/
def CameronMartinMetricEventTransferFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ) (f : ℂ → ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ z : ℂ, ‖z‖ = 1 → f z = 0) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (B : (ℂ → ℂ → ℝ) → Prop),
  IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  NullMeasurableSet {ω | B (fun x y => (weylScaling (D ω) ξ f x y).toReal)} P →
  NullMeasurableSet {ω | B (D ω)} P →
  0 < P {ω | B (fun x y => (weylScaling (D ω) ξ f x y).toReal)} → 0 < P {ω | B (D ω)}

/-- FIRST-PASS FROZEN (EXTERNAL, proposed minimal correction of `CameronMartinMetricEventTransferFrozen`, truth check
`notes/fp-gaps/CHATGPT-CM-metric-truth.md` section 1: add the measurability of the predicate `B` in the product
σ-algebra on metrics; the Cameron-Martin absolute continuity `Law(e^{ξ f} D_h) ≪ Law(D_h)` gives the stated direction).
Acceptance is the operator's (ACCEPT check) and is pending. Same content as the superseded predicate, plus
`MeasurableSet {d | B d}`. -/
def CameronMartinMetricEventTransferMeasurableFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ) (f : ℂ → ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ z : ℂ, ‖z‖ = 1 → f z = 0) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (B : (ℂ → ℂ → ℝ) → Prop),
  MeasurableSet {d : ℂ → ℂ → ℝ | B d} →
  IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  NullMeasurableSet {ω | B (fun x y => (weylScaling (D ω) ξ f x y).toReal)} P →
  NullMeasurableSet {ω | B (D ω)} P →
  0 < P {ω | B (fun x y => (weylScaling (D ω) ξ f x y).toReal)} → 0 < P {ω | B (D ω)}

end HarmonicBalls
