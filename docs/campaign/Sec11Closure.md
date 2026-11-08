# Section 11 pinch closure (task z6-sec11-pinch-lemmas)

Written argument: `notes/sec11-proof/sec11-proof.tex` (draft lines 46–269 metric bridge, 271–311 fixed geometry, 376–446 mass–diameter step, 447–513 local certificate).
Frozen targets (read-only): `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`) and `ManyPinchScalesStmt` (Lemma 11.13, `:259`).

## Compiled (no sorry; axioms propext, Classical.choice, Quot.sound)

- `Proofs/Sec11/Closure/LocalCertificate.lean` (a2ed68e): `Sec11LocalPinchCertificateStmt`; `pinchEventPositiveProbabilityStmt_of_localCertificate`.
- `Proofs/Sec11/Closure/FixedGeometry.lean` (e2e776d) and `CorrectedFixedGeometry.lean` (d3badfd): fixed pinch configuration and corrected fixed configuration (`δ = 10⁻⁴`).
- `Proofs/Sec11/Closure/MassDiameterInside.lean` (731abb6) and `FixedMassDiameter.lean` (1c9557d): `hinside` for admissible squares, and the fixed-geometry instance.
- `Proofs/Sec11/Closure/MetricBridgeZero.lean` (76bb7bd) and `MetricMeasurableZero.lean` (a99704b): the zero-charge metric bridge for `Ω : Type`.
- `Proofs/Sec11/Closure/PinchEventTypeZero.lean` (209b0b2): the body of `PinchEventPositiveProbabilityStmt` at `α₀ = 0` for `Ω : Type`, from the named premises `RawCanonicalPositiveStmt` and `haem`; the staged `LQGMetricFieldAxioms` is not used.

## Suspected gap (operator)

- F3. The first-event quantities `L = D(cl Q', ∂Q)` (line 316) and `a₀ = D(0, ∂B_d)` (line 320) are full-metric quantities (`D = D_{h^α}`, line 314). The assertion that they are measurable outside `W` (lines 490–491) is not justified by the locality axiom.

## Open premises

- RAW. `RawCanonicalPositiveStmt` quantifies over every `ξ`; the conditional chain supplies it only for `ξ > 0`. R0 must cover this premise too.
- F4 (`haem`). `AEMeasurable μ P` for the measure-valued field: the repository has open-set evaluations only (`Proofs/Sec6/PotentialRatioAEMeasurable.lean:109`), which use the staged `LQGMeasureLocality`.
- T1. `SquareDyadicTailInput`: the square diameter moment or tail, Pfeffer [P] Prop. 4.6 (arXiv:2104.04020v3). Not staged in `Proposed/`. `Steps/Sec11/NormalizedDiameterPositiveMoment.lean` converts positive moments into tails.
- F1. `hfront`: `μ_h(∂ closedSquare) = 0` a.s. needs `μ_h ≪ Lebesgue`; `IsLQGLimit` is Radon plus vague limit only.
- F2. Measurable clause of `hinside`: the producer gives `NullMeasurableSet` only.
- R0 (operator). `ξ > 0` (no positivity field in `IsLQGMetric` or `SatisfiesLQGMetricAxioms`, `Defs/LQGMetric.lean:146,179`).
- R7 (operator). `IsLQGMetric` axioms quantify over `Ω : Type`; the target over `Ω : Type*`.
- R2. `LQGVolumeGrowthAllScalesStmt.{0}` (`Draft/Section2.lean:122`) follows from `LiouvilleBallMassBoundStep` (`Steps/Sec2/VolumeGrowth.lean:69`); supplies `hfull`.
- R5. The Audit consumer (`Audit/Section11PinchMetricFieldConsumer.lean:83`) still takes the staged `LQGMetricFieldAxioms` (`Proposed/LQG.lean:199`).
- R1. General-`α` local certificate (`CorrectedPinchFrequency.lean:106`).
- R6. Cameron–Martin steps: not verified against the written argument.

## Inputs

No new Proposed or External statements were added in this task.
