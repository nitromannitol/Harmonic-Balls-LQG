# Section 6 full thirteen-result conjunction: frozen export audit

Worker z4, task section6-full-three-input-frozen-export-audit (Round 8).
Status: builds and guard passes. Source review of the three staged Proposed inputs is PENDING (operator). This is a reduction, not numbered closure.

Credit: Leonardo Bonanno. The annulus iteration (`annulusIterationStmt_proved`) and the Gwynne–Miller lemma route run through his proof in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. LatticeProb reuse rests on the operator approval recorded in the task file (inbox Nov4 08:20 E35).

## Artifacts

- `HarmonicBalls/Proofs/Sec6/FullThreeInputAssembly.lean` (namespace `HarmonicBalls.Section6Full`): `section6Full_of_three_inputs` (the thirteen frozen statements in frozen order) and thirteen typed exports `<statement>_of_three_inputs`, each keeping the same three binders.
- `HarmonicBalls/Audit/Section6FullInputChecks.lean`: fourteen `#print axioms` lines and a guard (`#eval`) for constants, binders, conjunct order, consumption and closure.
- Not edited: Defs, Draft, FROZEN, Proposed, External, old providers, umbrella, and the Bonanno-free `Proofs/Sec6/ThreeInputAssembly.lean`.

## Route

`hDG`, `hCC`, `hE` give `lqgVolumeGrowthAllScalesStmt_of_staged_inputs` (`Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53`), which is the all-scales volume growth input I2. `wholePlaneGFFAffineInvariance_univ` (`Proofs/Sec3/DerivedInputAssembly.lean:55`) supplies affine invariance, Weyl scaling is proved inside the producer, and `hE Ω P γ 0` supplies the insertion-0 existence premise. All of this feeds `HarmonicBalls.Section6.section6_of_volumeGrowth` (`Proofs/Sec6/Section6FromVolumeGrowth.lean:21`).

## Premises (exactly three)

| Binder | Prop (binders in order) | Source |
|---|---|---|
| `hDG` | `WholePlaneLQGBallMassBounds P γ hC hcirc`, for all Ω P γ hC hcirc | `Proposed/LQG.lean:152` |
| `hCC` | `LQGMeasureCoordChange P γ 0 hC hcirc`, for all Ω P γ hC hcirc (insertion 0) | `Proposed/LQG.lean:114` |
| `hE` | `LQGMeasureExistence P γ α hC hcirc`, for all Ω P γ α hC hcirc (every α; α is the fifth of seven binders) | `Proposed/LQG.lean:66` |

The guard checks by `==` on binder domains: each premise equals the same premise of the I2 export, `hCC` equals the insertion-0 premise of `section6_of_volumeGrowth`, and every typed export has the same three domains as the main export.

## Frozen conjunction

Conjunct heads in order (`Draft/Section6.lean:206` to `:462`): HarnackTypeEstimateStmt, HarnackTypeComponentStmt, ManyGoodAnnuliStmt, GoodAnnulusProbabilityStmt, AnnulusIterationStmt, ManyVeryGoodAnnuliStmt, VeryGoodAnnulusProbabilityStmt, AnnulusMassBoundByOdometerStmt, OdometerHarmonicMeasureBoundStmt, OdometerBoundByAnnulusMassStmt, VeryGoodAnnulusHarnackTypeStmt, ShellDecompositionStmt, LowMassSmallOdometerStmt. The guard checks this list by constant name, and each typed export's conclusion head.

## Leaves hsub, 6.8, 6.10, 6.13: discharged in this route

These were left open in the Bonanno-free route (`ThreeInputAssembly.lean`). They are not premises here, and the Round 7 open question is resolved.

| Leaf | Closure producer (proved theorem) |
|---|---|
| hsub, `VeryGoodAnnuliSubRangeStep` (`Steps/Sec6/Prevalence.lean:54`) | `HarmonicBalls.Section6.veryGoodAnnuliSubRangeStep_of_volumeGrowth` |
| 6.8, `AnnulusMassBoundByOdometerStmt` | `HarmonicBalls.Section6.annulusMassBoundByOdometer_of_volumeGrowth` (`Proofs/Sec6/AnnulusMassOdometer.lean:103`), applied to `hgrowth` |
| 6.10, `OdometerBoundByAnnulusMassStmt` | `HarmonicBalls.Section6.odometerBoundByAnnulusMass_of_volumeGrowth` (`Proofs/Sec6/AnnulusOdometerAssembly.lean:13`), applied to `hgrowth` |
| 6.13, `LowMassSmallOdometerStmt` | `HarmonicBalls.Section6.lowMassSmallOdometerStmt_of_volumeGrowth` (`Proofs/Sec6/VolumeGrowthConsequences.lean:13`), applied to `hgrowth` |

Every frozen statement has at least one closure producer; the guard prints them by conclusion head.

## Printed constants and scans

- All fourteen exports print `[propext, Classical.choice, Quot.sound]` (lc log `logs/lc/031714-2026322.log`). The guard throws on any other constant, and the log has no `sorryAx` or `ofReduceBool`.
- Code scan of both Lean files: no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `unsafe` or `set_option`.
- `lb` builds `HarmonicBalls.Proofs.Sec6.FullThreeInputAssembly` and `HarmonicBalls.Audit.Section6FullInputChecks` with no warning naming either module.

## Closure (guard)

- 1980 HarmonicBalls declarations (3557 theorems) in 331 modules.
- LatticeProb modules reached: 194, including `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. `annulusIterationStmt_proved` reached: yes.
- Producer of the open Lemma 8.2 obligation (`TypicalPointManyGoodScalesStmt`) reached: no. The guard throws if it is.
- Proposed heads reached, with closure producers:
  - `WholePlaneGFFAffineInvariance`: `wholePlaneGFFAffineInvariance_proved`, `wholePlaneGFFAffineInvariance_univ`.
  - `LQGMeasureWeylScaling`: `Section6.lqgMeasureWeylScaling`.
  - `LQGMeasureNonatomic`: `Section6.lqgMeasureNonatomic_of_existence`, `Section6.lqgMeasureNonatomic_of_volumeGrowth`, `singular_nonatomic_of_existence_and_wholePlane`.
  - `LQGMeasureExistence`, `LQGMeasureCoordChange`, `WholePlaneLQGBallMassBounds`: no closure producer. These are the three premises.
- External heads reached: none.
- Auxiliary obligation: `HarmonicBalls.LQGMeasureExistence._proof_1`, a proof Lean abstracts from the definition body. It is not a hypothesis and is not a non-standard constant.
- Steps definitions reached: 44 (filter by module only; the list is in the log). This is a reading aid. The exports have no premise besides `hDG`, `hCC`, `hE`, and the kernel check excludes other free variables.

## Open items

1. Source review of `WholePlaneLQGBallMassBounds`, `LQGMeasureCoordChange` and `LQGMeasureExistence` is pending. They are the only premises of the exports.
2. The Bonanno route depends on the LatticeProb closure (194 modules). The operator approval recorded in the task file covers this reuse.
3. Nothing here is a new numbered closure claim. The exports are conditional on the three inputs.
