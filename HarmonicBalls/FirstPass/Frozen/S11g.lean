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

/-- FIRST-PASS FROZEN. Continuity of the internal metric on open sets (internal metric of Fact 2.2 I, Bou-Rabee-Gwynne
arXiv:2208.11795, corrected draft line 428, `Defs/LQGMetric.lean:65`): for a whole-plane LQG
metric `D` of a field `hC` (`IsLQGMetricOfField`, `α₀ = 0`, so `D = 𝔇(h^ℂ)` almost surely), every open `W ⊆ ℂ` and almost
surely in `ω`, the ENNReal-valued internal metric `(z, w) ↦ D^W(z, w)` is continuous on `W ×ˢ W` (the value `∞` is allowed
and is locally constant across components of `W`). The statement is per open `W` and almost surely (the weakest form used
by the countable reductions of pinch events). Standard; locator pending. Operator ruling 2026-11-09 18:50 UTC
(continuity on open sets, EXTERNAL). Used by: the measurability of the third event in `firstPass_11_17` (step N2). -/
def LQGInternalMetricContinuousFrozen : Prop :=
  ∀ (γ ξ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (D : Ω → ℂ → ℂ → ℝ), IsLQGMetricOfField P γ ξ 0 hC D →
    ∀ W : Set ℂ, IsOpen W →
      ∀ᵐ ω ∂P, ContinuousOn (fun p : ℂ × ℂ => internalMetric (D ω) W p.1 p.2) (W ×ˢ W)

/-- FIRST-PASS FROZEN. The length identity of an LQG metric (Fact 2.2 I, Bou-Rabee-Gwynne arXiv:2208.11795, corrected draft
line 428; the Euclidean length metric axiom `ofReal_eq_internalMetric` of `IsEuclideanLengthMetric`, `Defs/LQGMetric.lean`):
for an LQG metric `D` of a whole-plane field `hC` (`IsLQGMetricOfField`, `α₀ = 0`), almost surely for all `z w ∈ ℂ`,
`ENNReal.ofReal (D z w)` is the internal metric of `D` on the whole plane, i.e. the infimum of the `D`-lengths of paths
from `z` to `w` in `ℂ`. The statement is for the metric `D` itself (not for an arbitrary function). Standard; locator
pending. Used by: the measurability and continuity of the distance `ofReal (setDist D S₁ S₂)` in the third pinch event
(`FirstPass/S11h/ThirdEventMeasurable.lean`, step N2 of `firstPass_11_17`). -/
def LQGMetricLengthIdentityFrozen : Prop :=
  ∀ (γ ξ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (D : Ω → ℂ → ℂ → ℝ), IsLQGMetricOfField P γ ξ 0 hC D →
    ∀ᵐ ω ∂P, ∀ z w : ℂ, ENNReal.ofReal (D ω z w) = internalMetric (D ω) Set.univ z w

/-- FIRST-PASS FROZEN. Continuity of the internal metric on open sets for an LQG metric with insertion `α₀ < Q`: the
alpha-general form of `LQGInternalMetricContinuousFrozen` (which is the case `α₀ = 0`). For `0 < γ < 2`, `α₀ < lqgQ γ` and
an LQG metric `D` of `hC` (`IsLQGMetricOfField`, log-singular field `h^ℂ - α₀ log|·|`), every open `W ⊆ ℂ` and almost surely
in `ω`, `(z, w) ↦ D^W(z, w)` is continuous on `W ×ˢ W` (the value `∞` is allowed). Source: Dubédat-Falconet-Gwynne-Pfeffer-Sun
2020, arXiv:1905.00380, Theorem 1.10 (p. 10) and Proposition 3.17 (p. 43), with the internal metric of Bou-Rabee-Gwynne
arXiv:2208.11795, Fact 2.2 I (corrected draft line 428). Operator ruling 2026-11-09 21:12 UTC (B1, EXTERNAL); truth check
follows. Used by: `ae_continuous_metric_alpha`, `nullMeasurableSet_pinchThirdEvent_alpha` (FirstPass/S11h/ThirdEventAlpha.lean),
and through them `firstPass_11_17_corrected`. -/
def LQGInternalMetricContinuousAlphaFrozen : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (D : Ω → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
    IsLQGMetricOfField P γ ξ α₀ hC D →
    ∀ W : Set ℂ, IsOpen W →
      ∀ᵐ ω ∂P, ContinuousOn (fun p : ℂ × ℂ => internalMetric (D ω) W p.1 p.2) (W ×ˢ W)

/-- FIRST-PASS FROZEN. The length identity of an LQG metric with insertion `α₀ < Q`: the alpha-general form of
`LQGMetricLengthIdentityFrozen` (the case `α₀ = 0`). For `0 < γ < 2`, `α₀ < lqgQ γ` and an LQG metric `D` of `hC`
(`IsLQGMetricOfField`), almost surely for all `z w ∈ ℂ`, `ENNReal.ofReal (D z w)` is the internal metric of `D` on `ℂ`, i.e. the
infimum of the `D`-lengths of paths from `z` to `w`. Source: Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020, arXiv:1905.00380,
Theorem 1.10 (p. 10); Gwynne-Miller 2021, arXiv:1905.00383v3, Section 1.2 (metric axioms). Operator ruling 2026-11-09 21:12 UTC
(B1, EXTERNAL); truth check follows. Used by: `ae_continuous_metric_alpha`, `nullMeasurableSet_pinchThirdEvent_alpha`
(FirstPass/S11h/ThirdEventAlpha.lean), and through them `firstPass_11_17_corrected`. -/
def LQGMetricLengthIdentityAlphaFrozen : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (D : Ω → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
    IsLQGMetricOfField P γ ξ α₀ hC D →
    ∀ᵐ ω ∂P, ∀ z w : ℂ, ENNReal.ofReal (D ω z w) = internalMetric (D ω) Set.univ z w

end HarmonicBalls
