# Section 11 pinch closure (task z6-sec11-pinch-lemmas)

Written argument: `notes/sec11-proof/sec11-proof.tex` (draft lines 46–269 metric bridge, 271–311 fixed geometry, 447–513 local certificate).
Frozen targets (read-only): `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`) and `ManyPinchScalesStmt` (Lemma 11.13, `:259`).

## Compiled (no sorry; axioms propext, Classical.choice, Quot.sound)

- `Proofs/Sec11/Closure/LocalCertificate.lean` (a2ed68e)
  - `Sec11LocalPinchCertificateStmt`: the local-certificate form (draft lines 447–513) for every `α < lqgQ γ`, stated with `CorrectedLocalPinchCertificate` (`Proofs/Sec11/CorrectedPinchFrequency.lean:29`).
  - `pinchEventPositiveProbabilityStmt_of_localCertificate`: the certificate implies the frozen target at `α₀ = 0`.
- `Proofs/Sec11/Closure/FixedGeometry.lean` (e2e776d)
  - `isPinchPointConfiguration_fixed`: the explicit sets `U = B_{.01}(1.5)`, `Q' = B_{.04}(-4.4)`, `Q = B_{.1}(-4.4)`, `T = B_{.1}(1.5) ∪ {1.5<x<4.9, |y|<.05} ∪ 𝔸_{4.8,5}` form an `IsPinchPointConfiguration`.
  - `exists_isPinchPointConfiguration`: the existential witness of the target.

## Reused endpoints (existing, not re-proved)

- `Proofs/Sec11/PinchInnerPositivity.lean`: target from the raw strengthened positivity plus measurability and length-metric side conditions.
- `Proofs/Sec11/CorrectedPinchFrequency.lean`: `exists_local_internal_pinch_zeroCharge` (`:144`, α = 0: raw positivity gives the local certificate); `exists_local_internal_pinch_of_metric_locality` (`:106`, general α, needs normalized data `c, G`).
- `Proofs/Sec11/CorrectedPinchConditionalPositive.lean:13`: raw positivity from `LQGVolumeGrowthAllScalesStmt.{0}`, `IsCorrectedPinchConfiguration`, `0 < ξ`, a functional `𝔇`, and the conditional mass–diameter positivity `hinside`.
- `Steps/Sec11/PinchLocalEvent.lean:108`: general-α local representative (fieldSigmaAlgebra, not mod constants), needs `LQGMeasureLocality` (`Proposed/LQG.lean:83`) and the staged `LQGMetricFieldAxioms` (`Proposed/LQG.lean:199`).
- `Audit/Section11PinchMetricFieldConsumer.lean:83`: consumer under the staged `LQGMetricFieldAxioms`.

## Open premises

- R0 (operator decision). The target quantifies over every `ξ : ℝ`. `IsLQGMetric` (`Defs/LQGMetric.lean:179`) has no positivity field, while the conditional chain needs `0 < ξ` (`CorrectedPinchConditionalPositive.lean:13`). The paper fixes `ξ = γ/d_γ > 0` (eq:xi, line 440). The frozen statement is not edited here.
- R1. General-`α` local certificate: no producer for arbitrary `α`; needs normalized data `c, G`.
- R2. `LQGVolumeGrowthAllScalesStmt.{0}` (`Draft/Section2.lean:122`) follows only from `LiouvilleBallMassBoundStep` (`Steps/Sec2/VolumeGrowth.lean:69`, paper Lemma 2.4, eq:ball-volume).
- R3. `hinside`: producers `ConditionalCoreMeasurability.lean:40`, `ConditionalCoreContainment.lean:43`, `ConditionalAbsoluteMassDiameter.lean:20`; premises not traced.
- R4. `IsCorrectedPinchConfiguration` (`Draft/Section11Corrected.lean:26`) for the fixed geometry: not yet built (needs `V, W`, the outer pieces, buffers and `pinchCorridor W Q δ`).
- R5. Metric bridge (draft lines 46–269) for an arbitrary metric map: only the staged `LQGMetricFieldAxioms`.
- R6. Cameron–Martin and mass–diameter steps (draft lines 447–513): partly in `Proofs/Sec11/CorrectedPinchFirst*.lean`, not verified against the written argument.

## Inputs

No new Proposed or External statements were added in this task.
