# Section 11 pinch closure (task z6-sec11-pinch-lemmas)

Written argument: `notes/sec11-proof/sec11-proof.tex` (draft lines 46–269 metric bridge, 271–311 fixed geometry, 376–446 mass–diameter step, 447–513 local certificate).
Frozen targets (read-only): `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`) and `ManyPinchScalesStmt` (Lemma 11.13, `:259`).

## Compiled (no sorry; axioms propext, Classical.choice, Quot.sound)

- `Proofs/Sec11/Closure/LocalCertificate.lean` (a2ed68e): `Sec11LocalPinchCertificateStmt`; `pinchEventPositiveProbabilityStmt_of_localCertificate`.
- `Proofs/Sec11/Closure/FixedGeometry.lean` (e2e776d), `CorrectedFixedGeometry.lean` (d3badfd): the fixed and corrected fixed configurations.
- `Proofs/Sec11/Closure/MassDiameterInside.lean` (731abb6), `FixedMassDiameter.lean` (1c9557d), `FixedMassDiameterOutside.lean` (49b5f3b): `hinside` for admissible squares, and fixed-geometry instances (pinned sets `B(0, 6/5)` and the complement of a neighbourhood of `W`).
- `Proofs/Sec11/Closure/MetricBridgeZero.lean` (76bb7bd), `MetricMeasurableZero.lean` (a99704b): the zero-charge metric bridge for `Ω : Type`.
- `Proofs/Sec11/Closure/PinchEventTypeZero.lean` (209b0b2): the body of `PinchEventPositiveProbabilityStmt` at `α₀ = 0` for `Ω : Type`, from `RawCanonicalPositiveStmt` and `haem`.
- `Proofs/Sec11/Closure/FixedRawPositive.lean` (9e362b2): the raw strengthened positivity of the fixed corrected configuration for `ξ > 0`, from the conditional chain, with explicit leftovers.

## Suspected gap (operator)

- F3. The first-event quantities `L = D(cl Q', ∂Q)` (line 316) and `a₀ = D(0, ∂B_d)` (line 320) are full-metric quantities (`D = D_{h^α}`, line 314). The assertion that they are measurable outside `W` (lines 490–491) is not justified by the locality axiom. `CorrectedPinchFirstSecond.lean:12` takes this measurability as hypothesis `hA`; R6 inherits F3, and so does `FixedRawPositive`.

## Open premises (named leftovers in `FixedRawPositive.lean`)

- hgrowth: `LQGVolumeGrowthAllScalesStmt.{0}` (`Draft/Section2.lean:122`), via `LiouvilleBallMassBoundStep` (`Steps/Sec2/VolumeGrowth.lean:69`).
- hfront (F1): `μ_h(∂ closedSquare) = 0` a.s.; needs `μ_h ≪ Lebesgue`, not in the repository.
- hdata (T1): `SquareDyadicTailInput`, Pfeffer [P] Prop. 4.6 (arXiv:2104.04020v3), not staged. `Steps/Sec11/NormalizedDiameterPositiveMoment.lean` gives tails from positive moments.
- hmeasIns (F2): the measurable clause of `hinside`; the producer gives `NullMeasurableSet` only.
- hm: measurability of the pinned σ-algebra (`localModConstPairings`, `Proofs/Sec11/ModConstPairingLaw.lean:19`); routine, not yet proved.
- A, hA, hArep, ha, hb: the first event measurable with respect to the pinned σ-algebra (F3).
- RAW for all `ξ` (`RawCanonicalPositiveStmt`): the chain gives `ξ > 0` only.
- F4 (`haem`): `AEMeasurable μ P`; only open-set evaluations exist (`Proofs/Sec6/PotentialRatioAEMeasurable.lean:109`, using the staged `LQGMeasureLocality`).
- R0 (operator). `ξ > 0`: no positivity field in `IsLQGMetric` or `SatisfiesLQGMetricAxioms` (`Defs/LQGMetric.lean:146,179`).
- R7 (operator). `IsLQGMetric` axioms over `Ω : Type`; the target over `Ω : Type*`.
- R5. The Audit consumer (`Audit/Section11PinchMetricFieldConsumer.lean:83`) still takes the staged `LQGMetricFieldAxioms`.
- R1. General-`α` local certificate (`CorrectedPinchFrequency.lean:106`).

## Inputs

No new Proposed or External statements were added in this task.
