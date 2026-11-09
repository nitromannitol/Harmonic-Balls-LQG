import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric

/-!
# First-pass frozen inputs for Lemma 11.17 (fp-S11h, owner n2)

FIRST-PASS FROZEN inputs for `firstPass_11_17` (paper `lemma:third-event-proof`, corrected draft lines 3726-3756).
Each is a `def ... : Prop` (never an axiom). Only general LQG metric background is frozen here; nothing about the
pinch configuration is frozen.
-/

universe u

namespace HarmonicBalls

open MeasureTheory

/-- FIRST-PASS FROZEN. The LQG metric axioms (paper Fact 2.2 I-IV, corrected draft lines 418-457) for a whole-plane GFF
plus a random continuous function, on a probability space in an arbitrary universe `Type u`. The Defs field
`IsLQGMetric.satisfiesLQGMetricAxioms` (`Defs/LQGMetric.lean:183`) quantifies over `Ω : Type` only; this Prop is the same
statement for every universe. General LQG background, not specific to the harmonic-ball paper; the statement is about the
joint law of the field and the metric and does not depend on the universe of the sample space. Source: Dubedat-Falconet-
Gwynne-Pfeffer-Sun 2020, arXiv:1905.00380, Theorem 1.10 and Proposition 3.17 (the metric axioms); Gwynne-Miller 2021,
Theorem 1.2 (p. 6). Locator pending. Phase 2: derivable by a canonical pushforward along a universe-lifting map
(n2 estimate 400-800 lines). Used by: ae_wholePlane_weylScaling_shift_univ (FirstPass/S11h/WeylShiftUniv.lean), and
through it firstPass_11_17. -/
def LQGMetricSatisfiesAxiomsUnivFrozen : Prop :=
  ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (f : Ω → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → (∀ ω, Continuous (f ω)) →
    (∀ x, Measurable fun ω => f ω x) →
    SatisfiesLQGMetricAxioms P γ ξ 𝔇 (fun ω => addFunPairing (hC ω) (f ω))

end HarmonicBalls
