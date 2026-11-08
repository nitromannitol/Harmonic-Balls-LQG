# Section 5 staged-input assembly

Task `section5-derived-staged-input-assembly` (worker z4, Claude Haiku 5.5). Credit: Leonardo Bonanno, whose work
enters through the imported modules (named in the module headers).

Files (new): `HarmonicBalls/Proofs/Sec5/StagedInputAssembly.lean` (exports), `HarmonicBalls/Audit/Section5StagedChecks.lean`
(typed, insertion-scope, axiom and consumption checks).

Status: the reduction compiles (lc and lb pass). It is not a numbered closure of Section 5, and it is not a
source-fidelity verdict. Results 5.2-5.5 remain conditional on the open leaves listed below.

## 1. Inputs

| Name | Statement (Lean) | Use | Source status |
| --- | --- | --- | --- |
| `hDG` | `WholePlaneLQGBallMassBounds` (`Proposed/LQG.lean:152`) | all exports | source-checked, operator 2026-11-08 05:00 UTC |
| `hCC` at insertion `0` | `LQGMeasureCoordChange P γ 0` | 5.1, 5.2, 5.3, 5.4, 5.6, 5.8 | source-checked (`Proposed/LQG.lean:114`) |
| `hCC` at every insertion | `∀ {Ω} P γ α₀, LQGMeasureCoordChange P γ α₀` | 5.5, 5.7 | same definition, general `α₀` |
| `hE` | `LQGMeasureExistence P γ α` at every `α` (`Proposed/LQG.lean:66`) | all exports | source-checked |
| `hTyp` | `TypicalPointManyGoodScalesStmt` (Lemma 8.2, `Draft/Section8.lean:74`) | 5.2, 5.3, 5.4, 5.5 | OPEN leaf, binder |
| `hBT` | `ClusterBoundaryTouchingRightContinuityStep` (`Steps/Sec5/ContinuityAssembly.lean:19`, G12) | 5.2 | OPEN leaf, binder, no producer |

The insertion-zero restriction `coordChange_zero_of_all_insertions` (`StagedInputAssembly.lean:163`) is the only
place where the all-insertion hypothesis is specialised. It feeds the producers of I2, Lemma 2.4 and Proposition 6.1,
which are stated at insertion `0`. No export takes an insertion-zero hypothesis in place of the all-insertion one.

## 2. Derived inside the module (not binders)

| Input | Lean name (file:line) | Producer used | Premises |
| --- | --- | --- | --- |
| I2 `LQGVolumeGrowthAllScalesStmt` (`Draft/Section2.lean:122`) | `volumeGrowthI2_of_staged_inputs` (`:77`) | `lqgVolumeGrowthAllScalesStmt_of_staged_inputs` (`Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53`) | `hDG`, `hCC` at `0`, `hE`; affine invariance proved (`wholePlaneGFFAffineInvariance_univ`) |
| Lemma 2.4 `LiouvilleVolumeGrowthStmt` (`Draft/Section2.lean:89`, with the [C1] ranges) | `liouvilleVolumeGrowth_of_staged_inputs` (`:83`) | `liouvilleVolumeGrowthStmt_of_existence` (`Proofs/Sec9/LQGExistenceConsequences.lean:30`) | `hDG`, `hCC` at `0`, `hE` |
| Proposition 6.1 `HarnackTypeEstimateStmt` (`Draft/Section6.lean:206`) | `harnackTypeEstimate_of_staged_inputs` (`:88`) | `Section6Full.harnackTypeEstimateStmt_of_three_inputs` (`Proofs/Sec6/FullThreeInputAssembly.lean:56`) | `hDG`, `hCC` at `0`, `hE` |

Route choice for Lemma 2.4. `Proofs/Sec2/Assembly.lean:116` (`liouvilleVolumeGrowthStmt_of_literature`) also takes
`hAff`, `hW` (`LQGMeasureWeylScaling` at `α₀ = 0`) and `hN` (`LQGMeasureNonatomic`) as premises. The Sec9 provider
discharges those from the three staged inputs: `hAff` is `wholePlaneGFFAffineInvariance_proved`, `hW` is
`Section6.lqgMeasureWeylScaling` (`Proofs/Sec6/LQGWeylScaling.lean:124`, a theorem with no premise), and `hN` is
`Section6.lqgMeasureNonatomic_of_existence` (`Proofs/Sec6/SingularityOriginNonatomic.lean:94`) applied to the scaled
mass step built from `hDG` and `hCC`. The premise set of the provider is therefore exactly `{hDG, hCC at 0, hE}`, so
the Sec2 provider is not used.

## 3. Exports

| Result (Draft) | Lean name (`StagedInputAssembly.lean`) | Binders, in order | Conclusion | Open leaves |
| --- | --- | --- | --- | --- |
| Prop 5.1 `ClusterUpperBoundStmt` (`Draft/Section5.lean:122`) | `section5_1_of_staged_inputs` (`:92`) | `hDG hCC0 hE` | frozen | none |
| Prop 5.2 `ClusterContinuityStmt` (`:140`) | `section5_2_of_staged_inputs` (`:102`) | `hDG hCC0 hE hTyp hBT` | frozen | `hTyp`, `hBT` |
| Prop 5.3 `ClusterBoundaryMeasureZeroStmt` (`:155`) | `section5_3_of_staged_inputs` (`:119`) | `hDG hCC0 hE hTyp` | frozen | `hTyp` |
| Prop 5.4 `RegularizedClusterHarmonicBallsStmt` (`:175`) | `section5_4_of_staged_inputs` (`:128`) | `hDG hCC0 hE hTyp` | frozen | `hTyp` |
| Thm 5.5 `ExistenceHarmonicBallsStmt` (`:192`) | `section5_5_of_staged_inputs` (`:189`) | `hDG hCC(all) hE hTyp` | frozen | `hTyp` |
| Prop 5.6 `UniquenessHarmonicBallsStmt` (`:206`) | `section5_6_of_staged_inputs` (`:146`) | `hDG hCC0 hE` | frozen | none |
| Lemma 5.7 `ClusterScaleInvarianceStmt` (`:226`) | `section5_7_of_staged_inputs` (`:183`) | `hDG hCC(all) hE` | frozen | none |
| Lemma 5.8 `ClusterStrongCompatibilityStmt` (`:246`) | `section5_8_of_staged_inputs` (`:153`) | `hDG hCC0 hE` | frozen | none (E51 open, section 5) |

The conclusions are the frozen Draft statements; no statement or definition was changed. The binder types are those of
the staged inputs as written in `Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53-57` and `Proposed/LQG.lean`.

## 4. Checks

* `lc` CHECK OK on `StagedInputAssembly.lean` (log `065317-2255114`) and on `Section5StagedChecks.lean` (log `065528-2261252`).
* `lb` BUILD OK on `HarmonicBalls.Proofs.Sec5.StagedInputAssembly` (log `065332-2256075`, no messages from the file) and on
  `HarmonicBalls.Audit.Section5StagedChecks` (log `065545-2262001`, no error lines).
* Printed axioms: all 12 `#print axioms` lines of the audit print `[propext, Classical.choice, Quot.sound]`.
* Typed checks (`example`s in the audit): each export has the stated binder types, in the stated order, and the stated
  conclusion. The expected types are restated in the audit from the staged input statements, so a permuted or weakened
  binder fails to elaborate.
* Insertion scope (meta check): the coordinate-change binder is implicit in `Ω` for 5.5 and 5.7 and explicit for the others.
* Consumption (meta check): every binder of each export occurs in its proof body.
* Code scans of both new files: no `sorry`, `admit`, `native_decide`, `axiom`, `maxHeartbeats` override, `opaque`,
  `extern` or `unsafe`; no pending-status wording.

## 5. Open items (not closed here)

* B1 `ClusterBoundaryTouchingRightContinuityStep` (`Steps/Sec5/ContinuityAssembly.lean:19`, G12): no producer in the
  repository. It blocks 5.2. Owned by task `post-contact-boundary-control`.
* B2 `TypicalPointManyGoodScalesStmt` (Lemma 8.2, `Draft/Section8.lean:74`): no producer. Its providers need the proof
  obligation `hcomparison` (`Proofs/Sec9/RootedComparisonWeakUniqueness.lean:34-52`). It blocks 5.3, and 5.2, 5.4, 5.5 through
  Lemma 8.1.
* Lemma 2.4 is consumed in its Draft form, which carries the corrected exponent ranges [C1]
  (`Draft/Section2.lean:89-108`: `min ((2-γ)²/2) (γ(Q-α₀))` and `max ((2+γ)²/2) (γ(Q-α₀))`). The operator's
  source check (`audits/PROPOSED-LQG-SOURCE-CHECK-20261108.md`, lines 76-86) refutes the printed uncorrected ranges by the
  counterexample `γ = 1`, `Q = 5/2`, `α₀ = 12/5`: the printed range admits `β⁺ = 1/4` (below `(2-γ)²/2 = 1/2`), but
  the bound `μ_h(B_r(0)) ≤ r^{1/4}` then holds with probability tending to zero, because `log μ_h(B_r(0)) / log r → γ(Q-α₀) = 1/10` in probability. The corrected
  range `min(1/2, 1/10) = 1/10` excludes `β⁺ = 1/4`. The corrected TeX still displays the uncorrected ranges; paper edits
  wait for Ahmed.
* The all-insertion `LQGMeasureCoordChange` (5.5, 5.7) uses the definition at general `α₀`, which the operator
  checked as faithful (HB Fact 2.1 IV, (2.7), p. 9). Operator to confirm that the universal quantifier over `α₀` is
  the intended scope, as opposed to the insertions used in the paper.
* E51 (semantic, no change here): `Draft/Section4.lean:57-69` (`subharmonicBallTestClass` over arbitrary open `O`);
  `Defs/Green.lean:28-31, 70-74` (`greenFunction` junk value for non-Greenian `O`); `Draft/Section5.lean:103-107,
  114-116, 246-257` (`ClusterStrongCompatibilityStmt` over all bounded open `U`, G9). 5.8 is exported as the frozen
  statement, so E51 applies to it. Operator ruling needed.
* Compiling an export is not a source-fidelity verdict and not a closure verdict for 5.1-5.8.
