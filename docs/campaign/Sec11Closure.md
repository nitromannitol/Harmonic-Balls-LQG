# Section 11 pinch closure (task z6-sec11-pinch-lemmas)

Written argument: `notes/sec11-proof/sec11-proof.tex` (draft lines 46–269 metric bridge, 271–311 fixed geometry, 376–446 mass–diameter step, 447–513 local certificate).
Frozen targets (read-only): `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`) and `ManyPinchScalesStmt` (Lemma 11.13, `:259`).

## Compiled (no sorry; axioms propext, Classical.choice, Quot.sound)

- `Proofs/Sec11/Closure/LocalCertificate.lean` (a2ed68e): `Sec11LocalPinchCertificateStmt` (draft 447–513, all `α < lqgQ γ`); `pinchEventPositiveProbabilityStmt_of_localCertificate` (certificate implies the target at `α₀ = 0`).
- `Proofs/Sec11/Closure/FixedGeometry.lean` (e2e776d): `isPinchPointConfiguration_fixed`, `exists_isPinchPointConfiguration` (draft 271–311).
- `Proofs/Sec11/Closure/CorrectedFixedGeometry.lean` (d3badfd): `isCorrectedPinchConfiguration_fixed`, `exists_isCorrectedPinchConfiguration` (`V`, `W`, `δ = 10⁻⁴`, buffers, corridor).
- `Proofs/Sec11/Closure/MassDiameterInside.lean` (731abb6): `hinside_of_square_dyadic_tail` (`hinside` of the conditional chain for every `n > 0`, `k`, from the dyadic-core producer), with the leftover premise `SquareDyadicTailInput`.

## Reused endpoints (existing, not re-proved)

- `Proofs/Sec11/CorrectedPinchConditionalPositive.lean:13`: raw strengthened positivity from `LQGVolumeGrowthAllScalesStmt.{0}`, the corrected configuration, `0 < ξ`, the functional `𝔇`, and `hinside`.
- `Proofs/Sec11/ConditionalCoreMeasurability.lean:40`: the dyadic-core producer whose conclusion is the `hinside` event.
- `Proofs/Sec11/DyadicClosedSquareTail.lean:40`: the closed-square tail, whose hypothesis `hbound` is the input `SquareDyadicTailInput` must supply.
- `Proofs/Sec11/PinchInnerPositivity.lean`, `Proofs/Sec11/CorrectedPinchFrequency.lean` (`:29`, `:37`, `:106`, `:144`), `Steps/Sec11/PinchLocalEvent.lean:108`, `Audit/Section11PinchMetricFieldConsumer.lean:83`.

## Open premises

- `SquareDyadicTailInput` (leftover, `Closure/MassDiameterInside.lean`): the square internal-diameter tail. The written argument attributes it to Pfeffer [P] Prop. 4.6 (arXiv:2104.04020v3, draft lines 138–183). It is not staged in `Proposed/`.
- R0 (operator decision). The target quantifies over every `ξ : ℝ`. The conditional chain needs `0 < ξ`. `IsLQGMetric` (`Defs/LQGMetric.lean:179`) and `SatisfiesLQGMetricAxioms` (`:146`) have no positivity field. The paper fixes `ξ = γ/d_γ > 0` (eq:xi, line 440).
- R7 (operator decision, universe). `IsLQGMetric.satisfiesLQGMetricAxioms` quantifies over `Ω : Type`, while the target quantifies over `Ω : Type*`. No law-transfer lemma exists in the repository.
- R2. `LQGVolumeGrowthAllScalesStmt.{0}` (`Draft/Section2.lean:122`) follows only from `LiouvilleBallMassBoundStep` (`Steps/Sec2/VolumeGrowth.lean:69`, paper Lemma 2.4).
- R3 remaining: `hfull` (from R2), `0 < ξ` (R0), measurability of the `hinside` event, and the first event being measurable with respect to `comap (localModConstPairings 0 hC O)`.
- R5. Metric bridge (draft lines 46–269): only the staged `LQGMetricFieldAxioms` (`Proposed/LQG.lean:199`).
- R1. General-`α` local certificate: needs normalized data `c, G` (`CorrectedPinchFrequency.lean:106`).
- R6. Cameron–Martin steps (draft lines 447–513): covered by the raw chain; not verified against the written argument.

## Inputs

No new Proposed or External statements were added in this task.
