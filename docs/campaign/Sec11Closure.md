# Section 11 pinch closure (task z6-sec11-pinch-lemmas)

Written argument: `notes/sec11-proof/sec11-proof.tex` (draft lines 46–269 metric bridge, 271–311 fixed geometry, 376–446 mass–diameter step, 447–513 local certificate).
Frozen targets (read-only): `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`) and `ManyPinchScalesStmt` (Lemma 11.13, `:259`).

## Compiled (no sorry; axioms propext, Classical.choice, Quot.sound)

- `Proofs/Sec11/Closure/LocalCertificate.lean` (a2ed68e); `FixedGeometry.lean` (e2e776d); `CorrectedFixedGeometry.lean` (d3badfd).
- `Proofs/Sec11/Closure/MassDiameterInside.lean` (731abb6), `FixedMassDiameter.lean` (1c9557d), `FixedMassDiameterOutside.lean` (49b5f3b): `hinside` for admissible squares and fixed-geometry instances.
- `Proofs/Sec11/Closure/MetricBridgeZero.lean` (76bb7bd), `MetricMeasurableZero.lean` (a99704b): the zero-charge metric bridge for `Ω : Type`.
- `Proofs/Sec11/Closure/PinchEventTypeZero.lean` (209b0b2): the body of the target at `α₀ = 0` for `Ω : Type`, from `RawCanonicalPositiveStmt` and `haem`.
- `Proofs/Sec11/Closure/FixedRawPositive.lean` (9e362b2), `FixedRawPositiveStaged.lean` (3a90d59), `PinchedSigmaLe.lean` (fa4ff84): the raw strengthened positivity of the fixed corrected configuration for `ξ > 0`. The volume-growth input is derived from the staged inputs `hDG`, `hCC`, `hE` (`Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53`); the pinned-σ-algebra premise is proved.

## Round 10: T1 source check and reduction (no Lean change; nothing admitted or staged)

- Source: Pfeffer, arXiv:2104.04020v3, Proposition 4.6 (p. 54) and eq. (4.9) (p. 55), checked on the rendered pages. Statement: `h` a whole-plane GFF normalized so that `h_1(0) = 0`; for each `p` a deterministic `C_p > 0`; `X` Borel in `𝕊 = [0,1]²` with `|𝒮^n(X)| ≤ T 2^{xn}`; then for every `p < ξ^{-1}(Q + √(Q² − 2x))` and every `𝔯 > 0`, `E[(𝔠_𝔯^{-1} e^{-ξ h_𝔯(0)} sup_{u,v∈X} D_h(u,v; 𝔯𝕊))^p] ≤ T C_p`.
- `𝔠_𝔯` is the constant of Axiom V (Pfeffer Def. 1.6, pp. 5–6, eq. (1.7)); `c_r = r^{ξQ+o(1)}` (lines 736, 1225 of the text).
- Lean facts checked: `IsLQGMetric` carries Axioms I–IV only (`Defs/LQGMetric.lean:146–160`), with no Axiom V. Lean III and IV give exactly `D_h(ru+z, rv+z) = r^{ξ·lqgQ γ} D_{h(r·+z)}(u,v)`. `IsWholePlaneGFF` fixes `h_1(0) = 0` almost surely (`Defs/GFF.lean:195`, `ae_circleAverage_one_zero`), and `wholePlaneGFFCov` (`Defs/GFF.lean:34–38`) gives the Gaussian structure of circle averages.
- Obligations for `SquareDyadicTailInput`:
  - O1 (normalization): closed at the statement level. The threshold factor `exp(ξ · hcirc ω 1 0)` equals 1 a.s., so the tail is a statement about the normalized field. No Lean lemma written yet.
  - O4 (normalization constant): reducible to provable steps. Any Axiom-V constant satisfies `c_r = K_r · r^{ξ lqgQ γ}` with `K_r ∈ [A⁻¹, A]` uniformly in `r`: the law of `r^{-ξQ} e^{-ξ h_r(0)} D(across rA)` does not depend on `r` (GFF scale invariance, proved provider `wholePlaneGFFAffineInvariance_univ`) and is non-degenerate, and tightness of the family and of its inverses confines `K_r`. Lean work not started.
  - O5 (closed square): translation and scaling move the normalization to `h_L(z)`, not `h_1(0)`. Needs O2.
  - O2 (circle averages at other centres and scales): not part of Prop 4.6. Comparing `e^{ξ h_r(z)}` with the origin normalization needs a Gaussian tail of circle averages, derivable from `wholePlaneGFFCov`. Not yet proved.
  - O3 (exponent): `Q(ξ) = lqgQ γ` follows from Prop 1.9 (`c_{δr}/c_r = δ^{ξQ(ξ)+o(1)}`) together with O4. For `x = 2` and `Q = lqgQ γ`, `Q + √(Q² − 4) = 4/γ`, so the window contains `p > 2` iff `γξ < 2` (`d_γ > γ²/2` for `ξ = γ/d_γ`). Unaudited bookkeeping: a Markov bound plus a Gaussian split of `h_𝔯(0)` gives `P(D > 𝔯^β) ≲ 𝔯^{ε²/2} + 𝔯^{p(ξ(Q−ε)−β)}`, which needs `(Q−2)(Q+√(Q²−4)) > 2`, i.e. `γ < 1`. This may be a loss of the crude route, not an obstruction. For h1 to audit before any Lean work.
- T1 is NOT closed. Nothing is admitted or staged in `Proposed/`, and `SquareDyadicTailInput` is unchanged.

## Suspected gap (operator)

- F3. The first-event quantities `L = D(cl Q', ∂Q)` (line 316) and `a₀ = D(0, ∂B_d)` (line 320) are full-metric quantities (`D = D_{h^α}`, line 314). The claim that they are measurable outside `W` (lines 490–491) is not justified by the locality axiom. `CorrectedPinchFirstSecond.lean:12` takes it as hypothesis `hA`; R6 inherits F3.

## Open premises

- hdata (T1): `SquareDyadicTailInput`; obligations O1–O5 above (O1 closed at statement level; O2, O3 analytic/audit; O4, O5 Lean work).
- hfront (F1): `μ_h(∂ closedSquare) = 0` a.s. needs `μ_h ≪ Lebesgue`; no staged Prop states it.
- hmeasIns (F2): the strict `MeasurableSet` clause of `hinside`; the producer gives `NullMeasurableSet` only (`ConditionalCoreMeasurability.lean:26`). The chain consumers take `MeasurableSet` (`CorrectedPinchFirstSecond.lean:28`, `CorrectedPinchFirstSecondGrowth.lean:30`).
- A, hA, hArep, ha, hb (F3): the first event measurable with respect to the pinned σ-algebra.
- R0 (operator; h1 audits ξ): `ξ > 0`; `RawCanonicalPositiveStmt` quantifies over every `ξ`.
- R7 (operator): `IsLQGMetric` axioms over `Ω : Type`; target over `Ω : Type*`.
- F4 (`haem`): `AEMeasurable μ P`; only open-set evaluations exist (staged `LQGMeasureLocality`).
- R5: the Audit consumer (`Audit/Section11PinchMetricFieldConsumer.lean:83`) still takes the staged `LQGMetricFieldAxioms`.
- R1: general-`α` local certificate (`CorrectedPinchFrequency.lean:106`).
- Staged Proposed inputs used (pending source-check): `hDG`, `hCC`, `hE` in `Proposed/LQG.lean`.

## Inputs

No new Proposed or External statements were added. Prop 4.6 is not staged.
