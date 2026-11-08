# Section 11 pinch closure (task z6-sec11-pinch-lemmas)

Written argument: `notes/sec11-proof/sec11-proof.tex` (draft lines 46–269 metric bridge, 271–311 fixed geometry, 447–513 local certificate).
Frozen targets (read-only): `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`) and `ManyPinchScalesStmt` (Lemma 11.13, `:259`).

## Compiled (no sorry; axioms propext, Classical.choice, Quot.sound)

- `Proofs/Sec11/Closure/LocalCertificate.lean` (a2ed68e): `Sec11LocalPinchCertificateStmt`, the local-certificate form (draft lines 447–513) for every `α < lqgQ γ`; `pinchEventPositiveProbabilityStmt_of_localCertificate`, which shows the certificate implies the frozen target at `α₀ = 0`.
- `Proofs/Sec11/Closure/FixedGeometry.lean` (e2e776d): `isPinchPointConfiguration_fixed`, `exists_isPinchPointConfiguration` (the explicit sets `U, T, Q', Q` of draft lines 271–311).
- `Proofs/Sec11/Closure/CorrectedFixedGeometry.lean` (d3badfd): `isCorrectedPinchConfiguration_fixed`, `exists_isCorrectedPinchConfiguration` (`V = B_{.02}(1.5)`, `W = B_{.04}(1.5)`, `δ = 10⁻⁴`; buffer fields by distance estimates; corridor field by connectedness of the segment `[0, 5i]` and the circle of radius 5 inside `B₇` minus the obstacle closures).

## Reused endpoints (existing, not re-proved)

- `Proofs/Sec11/CorrectedPinchConditionalPositive.lean:13`: raw strengthened positivity from `LQGVolumeGrowthAllScalesStmt.{0}`, `IsCorrectedPinchConfiguration` (now available), `0 < ξ`, a functional `𝔇`, and the conditional mass–diameter positivity `hinside`.
- `Proofs/Sec11/PinchInnerPositivity.lean`: target from the raw positivity plus measurability and length-metric side conditions.
- `Proofs/Sec11/CorrectedPinchFrequency.lean`: `exists_local_internal_pinch_zeroCharge` (`:144`, `α = 0`); `exists_local_internal_pinch_of_metric_locality` (`:106`, general `α`, needs normalized data `c, G`).
- `Steps/Sec11/PinchLocalEvent.lean:108`: general-`α` local representative (fieldSigmaAlgebra), needs `LQGMeasureLocality` (`Proposed/LQG.lean:83`) and the staged `LQGMetricFieldAxioms` (`Proposed/LQG.lean:199`).
- `Audit/Section11PinchMetricFieldConsumer.lean:83`: consumer under the staged `LQGMetricFieldAxioms`.

## Open premises

- R0 (operator decision). The target quantifies over every `ξ : ℝ`. The conditional chain needs `0 < ξ` (`CorrectedPinchConditionalPositive.lean:13`). `IsLQGMetric` (`Defs/LQGMetric.lean:179`) and `SatisfiesLQGMetricAxioms` (`:146`) have no positivity field. The paper fixes `ξ = γ/d_γ > 0` (eq:xi, line 440). The frozen statement is not edited here.
- R1. General-`α` local certificate: no producer for arbitrary `α`; needs normalized data `c, G` (`CorrectedPinchFrequency.lean:106`).
- R2. `LQGVolumeGrowthAllScalesStmt.{0}` (`Draft/Section2.lean:122`) follows only from `LiouvilleBallMassBoundStep` (`Steps/Sec2/VolumeGrowth.lean:69`, paper Lemma 2.4, eq:ball-volume).
- R3. `hinside`: producers `ConditionalCoreMeasurability.lean:40`, `ConditionalCoreContainment.lean:43`, `ConditionalAbsoluteMassDiameter.lean:20`; premises not traced.
- R5. Metric bridge (draft lines 46–269) for an arbitrary metric map: only the staged `LQGMetricFieldAxioms`.
- R6. Cameron–Martin and mass–diameter steps (draft lines 447–513): partly in `Proofs/Sec11/CorrectedPinchFirst*.lean`, not verified against the written argument.

## Inputs

No new Proposed or External statements were added in this task.
