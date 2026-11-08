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

## Round 14: F1 and R0 closed; fixed raw positivity without `hfront` and `0 < ξ`

- `Proofs/Sec11/Closure/FixedRawPositiveDerived.lean` (new, round 14): `fixed_raw_positive_null_of_staged_volume_growth_derived`, the type-zero raw positivity of the fixed corrected configuration with `hfront` and `0 < ξ` removed from the premises of `fixed_raw_positive_null_of_staged_volume_growth`. Build OK; axioms propext, Classical.choice, Quot.sound. Credit: Leonardo Bonanno (named in the module docstring for both producers).
- F1 closed, no new input: `hfront` is `IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero` (`Proofs/Sec11/FixedSquareFrontierNull.lean:347`; committed 960d3db and 0474ff2) applied to `hγ hγ₂ hμ fixedSquareCorner fixedSquareSide_pos.le`. The square is deterministic and fixed before `ω`.
- R0 closed, no new input: `0 < ξ` is `IsLQGMetric.weylExponent_pos h𝔇 hγ` (`Proofs/GFF/MetricXiSign.lean:360`; committed 0cbd0c3), with binders `(h𝔇) (hγ)`.
- Leftover premises of the fixed raw positivity: `hDG hCC hE` (staged, pending operator source-check); `hdata` (T1), with the applicability of the source metric `𝔇`; `A hA hArep ha hb` (F3); R1 (zero log-charge only: `hμ : IsLQGMeasureOfField P γ 0`); R7 (`Ω : Type`; transport to `Type*` not done). None of these is discharged here.
- Not claimed: closure of Lemma 11.12 (`PinchEventPositiveProbabilityStmt`) or of any numbered result.

## Round 13: F2 closed; F1 waits on z3; F3 and O5 reported (not closed)

- F2 (strict `MeasurableSet` clause of `hinside`), closed without new input (commit 39a2b06). `Closure/NullConditionalGrowth.lean`: `IsCorrectedPinchConfiguration.positive_wholePlane_first_second_of_growth_null` and `IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth_null`, the growth chains with `hinside` in `NullMeasurableSet`; they consume the existing null-measurable first-second chain `positive_wholePlane_first_second_null` (`Proofs/Sec11/CorrectedPinchFirstSecondNull.lean:12`). `Closure/FixedRawPositiveNull.lean`: `fixed_raw_positive_outside_null` (the clause is discharged by `IsWholePlaneGFF.nullMeasurableSet_mass_internalDiam`, `Proofs/Sec11/ConditionalCoreMeasurability.lean:26`, with `fixedU` open) and `fixed_raw_positive_null_of_staged_volume_growth` (volume growth from the staged `hDG hCC hE`; `hm` from `fixedPinnedSigma_le`). The strict theorems are unchanged. Axioms: propext, Classical.choice, Quot.sound.
- Leftover premises of the fixed raw positivity now: `hfront` (F1), `hdata` (T1, O2–O4 carried), `A hA hArep ha hb` (F3), `0 < ξ` (R0). `hgrowth`, `hm`, `hmeasIns` are discharged.
- F1 closes on the commit of z3's `IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero` (`Proofs/Sec11/FixedSquareFrontierNull.lean:333`, uncommitted in z3's tree when checked): `hgff hγ hγ₂ hμ fixedSquareCorner hL` gives `hfront`. No new input of mine; wiring waits for that commit.
- F3 (not closed; operator). `L = D(cl Q', ∂Q)` and `a₀ = D(0, ∂B_d)` (tex 313–324) use the full-plane metric `D = D_{h^α}`, an infimum over paths in ℂ. The written argument (tex 490–491) asserts that they are measurable outside `W`. Locality gives measurability of an internal metric `D_O` for open `O` disjoint from `W`, not of the global infimum, which can use paths through `W`. A repair needs a localization lemma (new mathematics) or a different event; route to the operator.
- O5 (not closed; needs O2 and a new step). Translation and scaling move the normalization to `h_L(z)`, so the threshold factor of `SquareDyadicTailInput z L` is `exp(ξ h_L(z))`, not `1`. Controlling it needs Gaussian tails or exponential moments of the circle averages `h_L(z)` (O2), and a tail-combination step for the random factor. Neither is in the written argument; no Lean started.
- `haem`: z3's `pinchEventPositive_typeZero_of_raw_gff` (`ClosureMeasureMeasurable.lean`, commit 88ef5d8) uses `IsWholePlaneGFF.aemeasurable_lqgMeasure` and no locality premise. The staged `LQGMeasureLocality` is therefore not needed for the type-zero body; the Round 12 route stays as an alternative.

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
- hfront (F1): CLOSED in round 14 by `IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero` (`FixedSquareFrontierNull.lean:347`) for the fixed square; no `μ ≪ Lebesgue` input is staged or used.
- hmeasIns (F2): CLOSED in round 13 for the null route (`fixed_raw_positive_outside_null`, `NullConditionalGrowth.lean`; producer `ConditionalCoreMeasurability.lean:26`). The strict-`MeasurableSet` chains (`CorrectedPinchFirstSecond.lean:28`, `CorrectedPinchFirstSecondGrowth.lean:30`) are unchanged.
- A, hA, hArep, ha, hb (F3): the first event measurable with respect to the pinned σ-algebra.
- R0: CLOSED in round 14 by `IsLQGMetric.weylExponent_pos` (`MetricXiSign.lean:360`, from `0 < γ`); see Round 14.
- R7 (operator): `IsLQGMetric` axioms over `Ω : Type`; target over `Ω : Type*`.
- R5: the Audit consumer (`Audit/Section11PinchMetricFieldConsumer.lean:83`) still takes the staged `LQGMetricFieldAxioms`.
- R1: general-`α` local certificate (`CorrectedPinchFrequency.lean:106`); needed by Lemma 11.13.
- Staged Proposed inputs used (pending source-check): `hDG`, `hCC`, `hE` in `Proposed/LQG.lean`, and `LQGMeasureLocality` (round 12, through `hLocal`).

## Inputs

No new Proposed or External statements were added. Prop 4.6 is not staged.
