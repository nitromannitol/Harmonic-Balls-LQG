# Section 11 pinch closure (task z6-sec11-pinch-lemmas)

Written argument: `notes/sec11-proof/sec11-proof.tex` (draft lines 46–269 metric bridge, 271–311 fixed geometry, 376–446 mass–diameter step, 447–513 local certificate).
Frozen targets (read-only): `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`; case α₀ = 0) and `ManyPinchScalesStmt` (Lemma 11.13, `:259`; general α₀).

## Compiled (no sorry; axioms propext, Classical.choice, Quot.sound)

- `Proofs/Sec11/Closure/LocalCertificate.lean` (a2ed68e): `Sec11LocalPinchCertificateStmt` (all α < lqgQ γ) and the reduction `pinchEventPositiveProbabilityStmt_of_localCertificate` (α₀ = 0).
- `Proofs/Sec11/Closure/FixedGeometry.lean` (e2e776d), `CorrectedFixedGeometry.lean` (d3badfd): the fixed and corrected fixed configurations.
- `Proofs/Sec11/Closure/MassDiameterInside.lean` (731abb6), `FixedMassDiameter.lean` (1c9557d), `FixedMassDiameterOutside.lean` (49b5f3b): `hinside` for admissible squares and fixed-geometry instances.
- `Proofs/Sec11/Closure/MetricBridgeZero.lean` (76bb7bd), `MetricMeasurableZero.lean` (a99704b): the zero-charge metric bridge for `Ω : Type`.
- `Proofs/Sec11/Closure/PinchEventTypeZero.lean` (209b0b2): the body of the target at `α₀ = 0` for `Ω : Type`, from `RawCanonicalPositiveStmt` and `haem`.
- `Proofs/Sec11/Closure/FixedRawPositive.lean` (9e362b2), `FixedRawPositiveStaged.lean` (3a90d59), `PinchedSigmaLe.lean` (fa4ff84): the raw strengthened positivity of the fixed corrected configuration for `ξ > 0`. The volume-growth input is derived from the staged inputs `hDG`, `hCC`, `hE` (`Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53`); the pinned-σ-algebra premise is proved.
- `Proofs/Sec11/Closure/TailNormalization.lean` (round 11): `ofReal_exp_mul_circleAverage_one_zero_ae` and `squareDyadicTailInput_iff_normalized`. Under `IsWholePlaneGFF` the threshold factor `e^{ξ h^ℂ_1(0)}` is `1` almost surely (`IsWholePlaneGFF.ae_circleAverage_one_zero`, `Defs/GFF.lean:195`), so `SquareDyadicTailInput` is equivalent to its normalized form. This closes obligation O1 in Lean.
- `Proofs/Sec11/Closure/RandomMeasureMeasurable.lean` (round 12): `aemeasurable_of_open_aemeasurable` (a family of finite-on-balls measures with a.e. measurable open-set evaluations is a.e. measurable for the Giry σ-algebra; Dynkin argument on the countable π-system `piQ`), `aemeasurable_lqg_measure_zero_of_locality` (the LQG measure is a.e. measurable from the staged `LQGMeasureLocality`), and `pinchEventPositive_typeZero_of_raw_locality` (the body of Lemma 11.12 at α₀ = 0 with the measurability premise `haem` replaced by the staged locality input `hLocal`).
- `HarmonicBalls.lean` imports the Closure modules (the import lines are owned by this task). `lc` passes.

## Round 12: F4 (`haem`) discharged from the staged locality input

- `haem` (`PinchEventTypeZero.lean:37–38`) asked for `AEMeasurable μ P` for the measure-valued field. Open-set measurability is `HarmonicBalls.Section6.aemeasurable_lqg_measure_open` (`Proofs/Sec6/PotentialRatioAEMeasurable.lean:109`), which uses the staged `LQGMeasureLocality` (`Proposed/LQG.lean:83`, Fact 2.1 II, paper line 405).
- The gap was the Mathlib σ-algebra on `Measure ℂ`: `Measure.measurable_of_measurable_coe` needs all measurable sets, and open-set measurability does not give them directly. Round 12 proves the extension (Dynkin argument on balls, countable π-system, modification on a measurable set of full measure). No new input is used.
- Consequence: the new theorem `pinchEventPositive_typeZero_of_raw_locality` takes the universal premise `hLocal : ∀ γ Ω P hC hcirc, LQGMeasureLocality P γ 0 hC hcirc` (the staged input) instead of `haem`. The original `pinchEventPositive_typeZero_of_raw` is unchanged. The staged input is pending operator source-check.
- `exists_measurable_pos_subset_pinch` (`PinchInnerPositivity.lean`) is owned by y1 and was not edited; the new theorem calls it as before.

## Round 10: T1 source check and reduction (no Lean change; nothing admitted or staged)

- Source: Pfeffer, arXiv:2104.04020v3, Proposition 4.6 (p. 54) and eq. (4.9) (p. 55), checked on the rendered pages. Statement: `h` a whole-plane GFF normalized so that `h_1(0) = 0`; for each `p` a deterministic `C_p > 0`; `X` Borel in `𝕊 = [0,1]²` with `|𝒮^n(X)| ≤ T 2^{xn}`; then for every `p < ξ^{-1}(Q + √(Q² − 2x))` and every `𝔯 > 0`, `E[(𝔠_𝔯^{-1} e^{-ξ h_𝔯(0)} sup_{u,v∈X} D_h(u,v; 𝔯𝕊))^p] ≤ T C_p`.
- `𝔠_𝔯` is the constant of Axiom V (Pfeffer Def. 1.6, pp. 5–6, eq. (1.7)); `c_r = r^{ξQ+o(1)}` (lines 736, 1225 of the text).
- Lean facts checked: `IsLQGMetric` carries Axioms I–IV only (`Defs/LQGMetric.lean:146–160`), with no Axiom V. Lean III and IV give exactly `D_h(ru+z, rv+z) = r^{ξ·lqgQ γ} D_{h(r·+z)}(u,v)`. `wholePlaneGFFCov` (`Defs/GFF.lean:34–38`) gives the Gaussian structure of circle averages.
- Obligations for `SquareDyadicTailInput`:
  - O1 (normalization): closed in Lean (round 11, `TailNormalization.lean`).
  - O4 (normalization constant): reducible to provable steps. Any Axiom-V constant satisfies `c_r = K_r · r^{ξ lqgQγ}` with `K_r ∈ [A⁻¹, A]` uniformly in `r`: the law of `r^{-ξQ} e^{-ξ h_r(0)} D(across rA)` does not depend on `r` (GFF scale invariance, proved provider `wholePlaneGFFAffineInvariance_univ`) and is non-degenerate, and tightness of the family and of its inverses confines `K_r`. Lean work not started. This bounded-ratio step is not in the paper and goes to the operator as new mathematics.
  - O5 (closed square): translation and scaling move the normalization to `h_L(z)`, not `h_1(0)`. Needs O2.
  - O2 (circle averages at other centres and scales): not part of Prop 4.6. Comparing `e^{ξ h_r(z)}` with the origin normalization needs a Gaussian tail of circle averages, derivable from `wholePlaneGFFCov`. Not yet proved; not in the paper.
  - O3 (exponent): `Q(ξ) = lqgQ γ` follows from Prop 1.9 (`c_{δr}/c_r = δ^{ξQ(ξ)+o(1)}`) together with O4. For `x = 2` and `Q = lqgQ γ`, `Q + √(Q² − 4) = 4/γ`, so the window contains `p > 2` iff `γξ < 2` (`d_γ > γ²/2` for `ξ = γ/d_γ`). Unaudited bookkeeping: a Markov bound plus a Gaussian split of `h_𝔯(0)` gives `P(D > 𝔯^β) ≲ 𝔯^{ε²/2} + 𝔯^{p(ξ(Q−ε)−β)}`, which needs `(Q−2)(Q+√(Q²−4)) > 2`, i.e. `γ < 1`. This may be a loss of the crude route, not an obstruction. For h1 to audit before any Lean work.
- T1 is NOT closed. Nothing is admitted or staged in `Proposed/`, and `SquareDyadicTailInput` is unchanged.

## Suspected gap (operator)

- F3. The first-event quantities `L = D(cl Q', ∂Q)` (line 316) and `a₀ = D(0, ∂B_d)` (line 320) are full-metric quantities (`D = D_{h^α}`, line 314). The claim that they are measurable outside `W` (lines 490–491) is not justified by the locality axiom. `CorrectedPinchFirstSecond.lean:12` takes it as hypothesis `hA`; R6 inherits F3.

## Open premises

- hLocal (round 12, replaces `haem`): the staged `LQGMeasureLocality` in its universal form, pending operator source-check (Fact 2.1 II, paper line 405).
- hdata (T1): `SquareDyadicTailInput`; O2, O3 (analysis and audit), O4 and O5 (Lean). O1 is closed.
- hfront (F1): `μ_h(∂ closedSquare) = 0` a.s. needs `μ_h ≪ Lebesgue`; no staged Prop states it.
- hmeasIns (F2): the strict `MeasurableSet` clause of `hinside`; the producer gives `NullMeasurableSet` only (`ConditionalCoreMeasurability.lean:26`). The chain consumers take `MeasurableSet` (`CorrectedPinchFirstSecond.lean:28`, `CorrectedPinchFirstSecondGrowth.lean:30`).
- A, hA, hArep, ha, hb (F3): the first event measurable with respect to the pinned σ-algebra.
- R0 (operator; h1 audits ξ): `ξ > 0`; `RawCanonicalPositiveStmt` quantifies over every `ξ`.
- R7 (operator): `IsLQGMetric` axioms over `Ω : Type`; target over `Ω : Type*`.
- R5: the Audit consumer (`Audit/Section11PinchMetricFieldConsumer.lean:83`) still takes the staged `LQGMetricFieldAxioms`.
- R1: general-`α` local certificate (`CorrectedPinchFrequency.lean:106`); needed by Lemma 11.13.
- Staged Proposed inputs used (pending source-check): `hDG`, `hCC`, `hE` in `Proposed/LQG.lean`, and `LQGMeasureLocality` (round 12, through `hLocal`).

## Inputs

No new Proposed or External statements were added. Prop 4.6 is not staged.
