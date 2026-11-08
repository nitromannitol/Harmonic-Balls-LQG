# Section 11 pinch closure (task z6-sec11-pinch-lemmas)

Written argument: `notes/sec11-proof/sec11-proof.tex` (draft lines 46–269 metric bridge, 447–513 local certificate).
Frozen targets (read-only): `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`),
`ManyPinchScalesStmt` (Lemma 11.13, `:259`).

## Compiled (no sorry, axioms propext, Classical.choice, Quot.sound)

- `HarmonicBalls/Proofs/Sec11/Closure/LocalCertificate.lean` (commit a2ed68e)
  - `Sec11LocalPinchCertificateStmt`: local-certificate form (draft lines 447–513) for every `α < lqgQ γ`,
    stated with `CorrectedLocalPinchCertificate` (`Proofs/Sec11/CorrectedPinchFrequency.lean:29`).
  - `pinchEventPositiveProbabilityStmt_of_localCertificate`: the certificate implies the frozen target at `α₀ = 0`.

## Reused endpoints (existing, not re-proved)

- `Proofs/Sec11/PinchInnerPositivity.lean`: target from the raw strengthened positivity
  `0 < P {pinchPointEventWithInternalBounds …}` plus measurability and length-metric side conditions.
- `Proofs/Sec11/CorrectedPinchFrequency.lean:144` `exists_local_internal_pinch_zeroCharge`: at `α = 0`, the raw
  positivity yields the local certificate.
- `Proofs/Sec11/CorrectedPinchFrequency.lean:106` `exists_local_internal_pinch_of_metric_locality`: general `α`,
  but needs normalized local data `c`, `G` with `hG`, `hGeq`.
- `Proofs/Sec11/CorrectedPinchConditionalPositive.lean:13` `positive_internal_pinch_of_conditional_growth`: raw positivity
  from `LQGVolumeGrowthAllScalesStmt.{0}`, `IsCorrectedPinchConfiguration`, a functional `𝔇`, and a conditional
  mass–diameter positivity hypothesis.
- `Audit/Section11PinchMetricFieldConsumer.lean:83`: consumer under the staged `LQGMetricFieldAxioms`
  (`Proposed/LQG.lean:199`, pending operator source-check).

## Open premises

- R1. General-`α` local certificate (`Sec11LocalPinchCertificateStmt` for all `α`). No producer for arbitrary `α`.
  Needs the normalized local metric data `c, G` (`CorrectedPinchFrequency.lean:106`).
- R2. `LQGVolumeGrowthAllScalesStmt.{0}` (`Draft/Section2.lean:122`) is only conditional:
  `Steps/Sec2/VolumeGrowth.lean:165` derives it from `LiouvilleBallMassBoundStep`. Status of that step not yet traced.
- R3. Conditional mass–diameter positivity (`hinside`). Producers: `Proofs/Sec11/ConditionalCoreMeasurability.lean:40`,
  `ConditionalCoreContainment.lean:43`, `ConditionalAbsoluteMassDiameter.lean:20`. Their core/shift premises not traced.
- R4. Metric bridge for an arbitrary metric map (draft lines 46–269): only the staged `LQGMetricFieldAxioms` exists.
- R5. Cameron–Martin and mass–diameter steps of draft lines 447–513: partly in `Proofs/Sec11/CorrectedPinchFirst*.lean`,
  not verified against the written argument.

## Inputs

No new Proposed or External statements were added in this task.
