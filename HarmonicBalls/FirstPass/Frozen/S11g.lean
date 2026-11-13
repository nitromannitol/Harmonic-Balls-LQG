import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric

/-!
# Frozen inputs for Lemma 11.17

FROZEN inputs for `firstPass_11_17` (paper `lemma:third-event-proof`, corrected draft lines 3726-3756).
Each is a `def ... : Prop` (never an axiom). Only general LQG metric background is frozen here; nothing about the
pinch configuration is frozen.
-/

universe u

namespace HarmonicBalls

open MeasureTheory

/-- FROZEN. The LQG metric axioms (paper Fact 2.2 I-IV, corrected draft lines 418-457) for a whole-plane GFF
plus a random continuous function, on a probability space in an arbitrary universe `Type u`. The Defs field
`IsLQGMetric.satisfiesLQGMetricAxioms` (`Defs/LQGMetric.lean:183`) quantifies over `Ω : Type` only; this Prop is the same
statement for every universe. General LQG background, not specific to the harmonic-ball paper; the statement is about the
joint law of the field and the metric and does not depend on the universe of the sample space. Source: Dubedat-Falconet-
Gwynne-Pfeffer-Sun 2020, arXiv:1905.00380, Theorem 1.10 and Proposition 3.17 (the metric axioms); Gwynne-Miller 2021,
Theorem 1.2 (p. 6). Locator pending. Phase 2: derivable by a canonical pushforward along a universe-lifting map
. Truth check TRUE:
it follows from the existing field `IsLQGMetric.satisfiesLQGMetricAxioms` by transferring the data to a `Type`-valued sample
space, pushing the GFF forward, and pulling back axioms I, III and each deterministic instance of IV; the single a.s. event of
axiom III carries all continuous shifts and endpoints. No literature input is added (the universe transfer is a
deduction, not a printed theorem; sources as cited above). Used by: ae_wholePlane_weylScaling_shift_univ (FirstPass/S11h/WeylShiftUniv.lean), and
through it firstPass_11_17. -/
def LQGMetricSatisfiesAxiomsUnivFrozen : Prop :=
  ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (f : Ω → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → (∀ ω, Continuous (f ω)) →
    (∀ x, Measurable fun ω => f ω x) →
    SatisfiesLQGMetricAxioms P γ ξ 𝔇 (fun ω => addFunPairing (hC ω) (f ω))

/-- FROZEN. Continuity of the internal metric on open sets for an LQG metric with insertion `α₀ < Q`, with the
whole-plane GFF hypothesis. For `0 < γ < 2`,
`α₀ < lqgQ γ`, if `∃ hcirc, IsWholePlaneGFF P hC hcirc` and `D` is an LQG metric of `hC` (`IsLQGMetricOfField`, log-singular
field `h^ℂ - α₀ log|·|`), then for every open `W ⊆ ℂ` and almost surely in `ω`, `(z, w) ↦ D^W(z, w)` is continuous on
`W ×ˢ W` (the value `∞` is allowed). Source: HB Fact 2.2(I) (arXiv:2208.11795, `fact:lqg-metric`: Euclidean topology and
length-metric property); Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020, arXiv:1905.00380v2, Theorem 1.10 (p. 10) and
Proposition 3.17 (p. 43) for the insertion range. Used by: `ae_continuous_metric_alpha` (FirstPass/S11h/ThirdEventAlpha.lean),
hence `nullMeasurableSet_pinchThirdEvent_alpha` and the faithful `firstPass_11_17_corrected`. -/
def LQGInternalMetricContinuousAlphaGFFFrozen : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (D : Ω → ℂ → ℂ → ℝ),
    (∃ hcirc : Ω → ℝ → ℂ → ℝ, IsWholePlaneGFF P hC hcirc) →
    0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMetricOfField P γ ξ α₀ hC D →
    ∀ W : Set ℂ, IsOpen W →
      ∀ᵐ ω ∂P, ContinuousOn (fun p : ℂ × ℂ => internalMetric (D ω) W p.1 p.2) (W ×ˢ W)

/-- FROZEN. The length identity of an LQG metric with insertion `α₀ < Q`, with the whole-plane GFF hypothesis.
If `∃ hcirc, IsWholePlaneGFF P hC hcirc`, `0 < γ < 2`, `α₀ < lqgQ γ` and `D` is
an LQG metric of `hC`, then almost surely for all `z w ∈ ℂ`, `ENNReal.ofReal (D z w)` is the internal metric of `D` on `ℂ`,
i.e. the infimum of the `D`-lengths of paths from `z` to `w`. Source: HB Fact 2.2(I) (arXiv:2208.11795, length-metric property);
Gwynne-Miller 2021, arXiv:1905.00383v3, Section 1.2 (axioms I-IV) and Theorem 1.2 (p. 6); Dubédat-Falconet-Gwynne-Pfeffer-Sun
2020, arXiv:1905.00380v2, Theorem 1.10 (p. 10). Used by: `ae_continuous_metric_alpha` and
`nullMeasurableSet_pinchThirdEvent_alpha` (FirstPass/S11h/ThirdEventAlpha.lean), hence `firstPass_11_17_corrected`. -/
def LQGMetricLengthIdentityAlphaGFFFrozen : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (D : Ω → ℂ → ℂ → ℝ),
    (∃ hcirc : Ω → ℝ → ℂ → ℝ, IsWholePlaneGFF P hC hcirc) →
    0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMetricOfField P γ ξ α₀ hC D →
    ∀ᵐ ω ∂P, ∀ z w : ℂ, ENNReal.ofReal (D ω z w) = internalMetric (D ω) Set.univ z w

/-- FROZEN. Deterministic metric geometry (closed-set exhaustion of the internal metric): for a Euclidean length
metric `D` and a closed set `C`, and `x, y ∈ C`, the internal metric of `C` is the infimum over `n` of the suprema over `k`
of the internal metrics of the open neighbourhoods `thickening ((k+1)⁻¹) (C ∩ closedBall 0 (n+1))`. Paths of `C` are
approximated by paths of the neighbourhoods; the length is lower semicontinuous under uniform convergence (Arzelà-Ascoli).
Source: standard; locator pending. Truth check TRUE (order inf_n sup_k, arc-length reparametrization of
near-minimizing paths); truth check TRUE exactly as written. Used by:
`corridorInternalSup_decoder` (FirstPass/S11h/CorridorSup11_17.lean), hence `pinchCertificateStmt_of_frozen`. -/
def InternalMetricClosedEqIInfThickeningFrozen : Prop :=
  ∀ (D : ℂ → ℂ → ℝ) (C : Set ℂ), IsClosed C → IsEuclideanLengthMetric D →
    ∀ {x y : ℂ}, x ∈ C → y ∈ C →
      internalMetric D C x y = ⨅ n : ℕ, ⨆ k : ℕ,
        internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) (C ∩ Metric.closedBall 0 ((n : ℝ) + 1))) x y

/-- FROZEN. Deterministic metric geometry (Euclidean property of a Weyl scaling): for a Euclidean length metric
`D` and a continuous compactly supported shift `f`, the Weyl-scaled metric `(weylScaling D ξ f).toReal` is again a
Euclidean length metric. The weights `exp (ξ f)` are bounded above and below, so the scaled metric is bi-Lipschitz to `D`,
and the length property follows from near-minimizing weighted curves. Source: standard; locator pending. Truth check TRUE
 (truth check TRUE exactly as written); EXTERNAL
deterministic metric fact. Used by: `pinchCertificateStmt_of_frozen`
(FirstPass/S11h/PinchCertificateProof11_17.lean), hence `firstPass_11_17`. -/
def WeylScaledEuclideanFrozen : Prop :=
  ∀ (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ), IsEuclideanLengthMetric D → Continuous f → HasCompactSupport f →
    IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal)

end HarmonicBalls
