# Section 11 pinch closure (task z6-sec11-pinch-lemmas)

Written argument: `notes/sec11-proof/sec11-proof.tex` (draft lines 46–269 metric bridge, 271–311 fixed geometry, 376–446 mass–diameter step, 447–513 local certificate).
Frozen targets (read-only): `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`) and `ManyPinchScalesStmt` (Lemma 11.13, `:259`).

## Compiled (no sorry; axioms propext, Classical.choice, Quot.sound)

- `Proofs/Sec11/Closure/LocalCertificate.lean` (a2ed68e): `Sec11LocalPinchCertificateStmt` (draft 447–513, all `α < lqgQ γ`); `pinchEventPositiveProbabilityStmt_of_localCertificate` (certificate implies the target at `α₀ = 0`).
- `Proofs/Sec11/Closure/FixedGeometry.lean` (e2e776d): `isPinchPointConfiguration_fixed`, `exists_isPinchPointConfiguration` (draft 271–311).
- `Proofs/Sec11/Closure/CorrectedFixedGeometry.lean` (d3badfd): `isCorrectedPinchConfiguration_fixed`, `exists_isCorrectedPinchConfiguration` (`δ = 10⁻⁴`, buffers, corridor).
- `Proofs/Sec11/Closure/MassDiameterInside.lean` (731abb6): `hinside_of_square_dyadic_tail` (`hinside` for any admissible square and pinned set, from the dyadic-core producer).
- `Proofs/Sec11/Closure/FixedMassDiameter.lean` (1c9557d): `fixed_hinside_of_square_dyadic_tail` (the instance for the fixed corrected geometry; geometric hypotheses proved).

## Open premises

- T1. `SquareDyadicTailInput` (`Closure/MassDiameterInside.lean`): the square internal-diameter tail. The written argument attributes it to Pfeffer [P] Prop. 4.6 (arXiv:2104.04020v3, draft lines 138–183). Not staged in `Proposed/`.
- F1. `hfront`: `μ_h(∂ closedSquare) = 0` almost surely. Needs `μ_h ≪ Lebesgue` almost surely; no such lemma in the repository. `Convex.addHaar_frontier` (Mathlib `Analysis/Convex/Measure.lean:35`) closes it once that is available.
- F2. The measurable clause of `hinside`: the producer gives only `NullMeasurableSet` (`Proofs/Sec11/ConditionalCoreMeasurability.lean:26`), while `hinside` (`Proofs/Sec11/CorrectedPinchConditionalPositive.lean:30`) asks for `MeasurableSet`.
- F3. The first event measurable with respect to `comap (localModConstPairings 0 hC O)` (`hA`, `ha`, `hb`): not traced for the fixed geometry.
- R0 (operator decision). The target quantifies over every `ξ : ℝ`. The conditional chain needs `0 < ξ`. `IsLQGMetric` (`Defs/LQGMetric.lean:179`) and `SatisfiesLQGMetricAxioms` (`:146`) have no positivity field. The paper fixes `ξ = γ/d_γ > 0` (eq:xi, line 440).
- R7 (operator decision, universe). `IsLQGMetric.satisfiesLQGMetricAxioms` quantifies over `Ω : Type`, while the target quantifies over `Ω : Type*`. No law-transfer lemma exists in the repository.
- R2. `LQGVolumeGrowthAllScalesStmt.{0}` (`Draft/Section2.lean:122`) follows from `LiouvilleBallMassBoundStep` (`Steps/Sec2/VolumeGrowth.lean:69`, paper Lemma 2.4); it supplies `hfull`.
- R5. Metric bridge (draft lines 46–269): only the staged `LQGMetricFieldAxioms` (`Proposed/LQG.lean:199`).
- R1. General-`α` local certificate: needs normalized data `c, G` (`CorrectedPinchFrequency.lean:106`).
- R6. Cameron–Martin steps (draft lines 447–513): covered by the raw chain; not verified against the written argument.

## Inputs

No new Proposed or External statements were added in this task.
