# Section 11 pinch closure (task z6-sec11-pinch-lemmas)

Written argument: `notes/sec11-proof/sec11-proof.tex` (draft lines 46–269 metric bridge, 271–311 fixed geometry, 376–446 mass–diameter step, 447–513 local certificate).
Frozen targets (read-only): `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`) and `ManyPinchScalesStmt` (Lemma 11.13, `:259`).

## Compiled (no sorry; axioms propext, Classical.choice, Quot.sound)

- `Proofs/Sec11/Closure/LocalCertificate.lean` (a2ed68e): `Sec11LocalPinchCertificateStmt`; `pinchEventPositiveProbabilityStmt_of_localCertificate`.
- `Proofs/Sec11/Closure/FixedGeometry.lean` (e2e776d) and `CorrectedFixedGeometry.lean` (d3badfd): the fixed pinch configuration and the corrected fixed configuration (`δ = 10⁻⁴`).
- `Proofs/Sec11/Closure/MassDiameterInside.lean` (731abb6): `hinside_of_square_dyadic_tail`; `Proofs/Sec11/Closure/FixedMassDiameter.lean` (1c9557d): `fixed_hinside_of_square_dyadic_tail`.
- `Proofs/Sec11/Closure/MetricBridgeZero.lean` (76bb7bd): at `α₀ = 0`, an arbitrary metric map with `IsLQGMetricOfField` agrees a.s. with the canonical `𝔇 (hC ω)`, and is a Euclidean length metric a.s. (for `Ω : Type`).
- `Proofs/Sec11/Closure/MetricMeasurableZero.lean` (a99704b): the same bridge in measurable form (`D'` with measurable entries, `D = D'` a.s.).

## Suspected gap (report to operator; no Lean change)

- F3. The first-event quantities `L = D(cl Q', ∂Q)` (written argument, line 316) and `a₀ = D(0, ∂B_d)` (line 320) are full-metric quantities (`D = D_{h^α}`, line 314). The assertion that the quantities of `E₁` are measurable outside `W` (lines 490–491) is not justified by the locality axiom. The chain requires `hA : MeasurableSet[comap (localModConstPairings 0 hC O)] A`. The representative lemma supplies measurability for `comap D` only.

## Open premises

- T1. `SquareDyadicTailInput` (`Closure/MassDiameterInside.lean`): the square internal-diameter tail, Pfeffer [P] Prop. 4.6 (arXiv:2104.04020v3). Not staged in `Proposed/`.
- F1. `hfront` (boundary-null square): needs `μ_h ≪ Lebesgue` a.s.; `IsLQGLimit` (`Defs/LQG.lean`) is only Radon plus vague limit.
- F2. Measurable clause of `hinside`: the producer gives `NullMeasurableSet` only.
- R0 (operator). The target quantifies over every `ξ : ℝ`; the chain needs `0 < ξ`. No positivity field in `IsLQGMetric` (`Defs/LQGMetric.lean:179`) or `SatisfiesLQGMetricAxioms` (`:146`).
- R7 (operator, universe). `IsLQGMetric` axioms quantify over `Ω : Type`; the target over `Ω : Type*`. The bridge above is for `Ω : Type` only.
- R2. `LQGVolumeGrowthAllScalesStmt.{0}` (`Draft/Section2.lean:122`) follows from `LiouvilleBallMassBoundStep` (`Steps/Sec2/VolumeGrowth.lean:69`); supplies `hfull`.
- R5. The Audit consumer (`Audit/Section11PinchMetricFieldConsumer.lean:83`) still takes the staged `LQGMetricFieldAxioms` (`Proposed/LQG.lean:199`).
- R1. General-`α` local certificate: needs normalized `c, G` (`CorrectedPinchFrequency.lean:106`).
- R6. Cameron–Martin steps: not verified against the written argument.

## Inputs

No new Proposed or External statements were added in this task.
