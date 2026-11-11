# LP staging area: index of `HarmonicBalls/LPStage`

Umbrella: `HarmonicBalls/LPStage/All.lean` imports the 54 LPStage modules of the table below (build with
`lb HarmonicBalls.LPStage.All`, BUILD OK 2026-11-11): the 37 earlier ones plus, added 2026-11-11, the 12 LQGMeasureNonatomic*
modules (z7), LQGMeasureFullSupport{,2,3} and LQGMeasureSquarePositive (z3, DONE 11:49) and WeylShiftedMass (z4, 10de7ef9).
Not imported: z4's LocalMeasureKernel{,2,3,4,5} (move-status notes and open items at the end of this file).
Row numbers are those of `docs/campaign/PHASE2-INVENTORY.md` section 2 (the 57 inputs; as in PHASE2-DERIVATION-STATUS.md).
"HB row" = the staged input; "support" = definitions or lemmas used by a staged result, no row of their own.
"Hypotheses": "none" = the main result takes no literature Prop; a definitional predicate (e.g. `IsWholePlaneGFF`) is not counted.
Line numbers are those of the committed files at the time of the row-56 commit.

| LPStage module | main result(s) (file:line) | HB row(s) | hypotheses | LPBridge file | move |
|---|---|---|---|---|---|
| BirkhoffErgodic | `ae_tendsto_birkhoffAverage_integral_of_ergodic` :155 (imports LP `Prob.Birkhoff`) | 7 | none | - | READY |
| CameronMartinDerived | support: `localFieldPairings` :36, `wholePlaneGFF_localFieldPairings_map_eq` :93 | support (13, 37) | none | - (via CameronMartinDerived2) | READY |
| CameronMartinDerived2 | `cameronMartinGFFReweighting_derived` :653; `cameronMartinGFFMutualAbsCont_derived` :869 | 37; 13 | none | FirstPass/LPBridge/CameronMartin.lean | READY |
| CircleAverageApprox | support: `circleDensity` :55, circle-density facts :59-75 | support | none | - (via CircleAverageApprox2) | READY |
| CircleAverageApprox2 | `IsWholePlaneGFF.isProbabilityMeasure` :20, `IsWholePlaneGFF.hasGaussianLaw_circle` :26, `ae_tendsto_circleApprox` :927 | support | none | - (via GFFAffineInvariance) | READY |
| GFF | base definitions: `CircleParameter` :42, `IsTestFunction` :46, `wholePlaneCov` :52, `IsAdmissible` :66, `eval` :71, `smear` :77 | none (base) | none | M1, M4, M5b | READY |
| GFFAffineInvariance | `wholePlaneGFFAffineInvariance_lp` :877 (def `WholePlaneGFFAffineInvarianceLP` :868) | 10 | none | FirstPass/LPBridge/GFFAffineInvariance.lean | READY |
| GFFCovSymm | `wholePlaneCovSymm_proved` :486 (`WholePlaneCovSymmStmt`); `exists_isWholePlaneGFF_of_psd` :500 | support (29) | `WholePlaneCovPSDStmt` (B2) remains | - | READY |
| GFFExistence | `exists_isWholePlaneGFF` :612; `kernelMatrix_posSemidef_of_psd` :539; `kolmogorovExtensionStmt_proved` :45 | 29 | B2 `WholePlaneCovPSDStmt` (:54) open; `KolmogorovExtensionStmt` discharged at :45 | - | READY |
| KolmogorovExtension | `exists_isProjectiveLimit_real` :197 (Kolmogorov extension, LP stage) | support (for `KolmogorovExtensionStmt`) | none | - | READY |
| LQGMassInner | `lqgMassInnerMeasurable_of_gff` :33 | 33 | none | FirstPass/LPBridge/LQGMassInner.lean | READY |
| LQGMeasure | support: `lqgQ` :34, `dyadicScale` :38, `lqgApprox` :43, `IsLQGLimit` :49, `IsLQGMeasure` :58 | support | none | M4 | READY |
| LQGMeasureDerived | `lqgMeasureOfProfileMeasurable_lp` :575 (def `LQGMeasureOfProfileMeasurableLP` :31) | 6 | none | FirstPass/LPBridge/LQGMeasureDerived.lean | READY |
| LQGMeasureFullSupport | `lqgMeasureFullSupportStmt_of_volumeGrowth_lp` :159 (def `LQGMeasureFullSupportStmtLP` :61) | 40 (LP form) | LP `LQGVolumeGrowthAllScalesStmtLP` (:50) as binder | FirstPass/LPBridge/LQGMeasureFullSupport.lean | READY |
| LQGMeasureFullSupport2 | support: `measure_le_of_rpow_norm_le` :40, `measure_ball_zero_le_of_dyadic` :76 | support (40) | none | - (via FullSupport3) | READY |
| LQGMeasureFullSupport3 | `lqgMeasureFullSupportStmt_of_scaled_lp` :398 (row 40 LP); `lqgVolumeGrowthAllScalesStmt_of_scaled_lp` :386 (row 50 LP); `liouvilleBallMassBoundStep_of_scaled_lp` :292 | 40; 50 | LP existence and non-atomicity binders (hS hE hN) | FirstPass/LPBridge/LQGMeasureFullSupport.lean (row 40) | READY |
| LQGMeasureInputs | LP forms of the Proposed inputs, as definitions: `LQGMeasureExistenceLP` :52, `LQGMeasureCoordChangeLP` :40, `WholePlaneLQGBallMassBoundsLP` :27 (no theorem) | 1; 2; 3 | LP literature Props, defined not proved | - | READY |
| LQGMeasureLocality | conditional `lqgLocality_of_circleLink` :410; defs `LQGLocality` :88, `LQGCircleAverageLink` :99 | 49 (conditional form) | `LQGCircleAverageLink` (:99); discharged by `lqgCircleAverageLink_of_gff` (LQGMeasureLocality2:151) | via LQGMeasureLocality2 bridge | READY |
| LQGMeasureLocality2 | unconditional `lqgLocality_of_gff` :171; `lqgCircleAverageLink_of_gff` :151 | 49 (unconditional) | none beyond `IsWholePlaneGFF` | FirstPass/LPBridge/LQGMeasureLocality.lean | READY |
| LQGMeasureNonatomic | `LQGMeasureNonatomicLP` :42 (def); `lqgMeasureNonatomic_lp` :49 | 4 (LP form of Proposed `LQGMeasureNonatomic`, Proposed/LQG.lean:77) | LP `WholePlaneLQGBallMassBoundsLP` (hDG), `LQGMeasureCoordChangeLP` (hCC, alpha=0), `LQGMeasureExistenceLP` (hE) | FirstPass/LPBridge/LQGMeasureNonatomicAll.lean (`lqgMeasureNonatomic_of_lp`) | READY |
| LQGMeasureNonatomicAll | `LQGMeasureNonatomicAllLP` :25 (def); `lqgMeasureNonatomicAll_lp` :30 | 41 (LP form) | the same three LP inputs | FirstPass/LPBridge/LQGMeasureNonatomicAll.lean (`lqgMeasureNonatomicAll_of_lp`) | READY |
| LQGMeasureNonatomicMassAffine | `affineMeasure_ball` :73; `isLQGMeasureOfField_affine` :86 | support (4, 41 chain) | binders as in file | - | READY |
| LQGMeasureNonatomicMassLocality | `restrict_eq_of_integral_eq_of_tsupport_subset` :61; `isLQGLimit_restrict_eq` :88 | support (41 chain) | binders as in file | - | READY |
| LQGMeasureNonatomicMassMixture | `mixMeasure_singleton` :60; `ae_mix_of_forall` :98 | support (41 chain) | binders as in file | - | READY |
| LQGMeasureNonatomicMassPoly | `polyHighProb_ae_eventually_dyadic` :88; `polyHighProb_dyadic_tail` :174 | support (41 chain) | binders as in file | - | READY |
| LQGMeasureNonatomicMassRescaled | `rescaledMeas_ball` :273; `rescaledBallMassUniformStep_lp` :287 | support (41 chain) | binders as in file | - | READY |
| LQGMeasureNonatomicMassScaled | `wholePlaneScaledBallMassStep_of_uniform_lp` :301; defs `RescaledBallMassUniformStepLP` :36, `WholePlaneScaledBallMassStepLP` :46 | support (41 chain) | binders as in file | - | READY |
| LQGMeasureNonatomicMassTail | `circleAverageDyadicTailStep_lp` :60 (def `CircleAverageDyadicTailStepLP` :32) | support (41 chain) | binders as in file | - | READY |
| LQGMeasureNonatomicMassWeight | `singularWeightStep_lp` :102 (def `SingularWeightStepLP` :29) | support (41 chain) | binders as in file | - | READY |
| LQGMeasureNonatomicMassWholePlane | `ae_wholePlane_nonatomic_of_scaledBallMass` :28; `ae_singular_nonatomic_off_origin_of_scaledBallMass` :84 | support (41 chain) | binders as in file | - | READY |
| LQGMeasureNonatomicOrigin | `origin_nonatomic_of_stronger_singularity` :131; `ae_origin_nonatomic_of_stronger_existence` :196 | support (41 chain) | binders as in file | - | READY |
| LQGMeasureSquare | `aemeasurable_lqgMeasure_borel` :121; `aemeasurable_lqgMeasure_open` :109 | 22 | `LQGLocality` (LP form of row 49 input) | FirstPass/LPBridge/LQGMeasureSquare.lean | READY |
| LQGMeasureSquarePositive | `lqgMeasureSquarePositiveLP_of_inputs` :86 (def `LQGMeasureSquarePositiveLP` :55) | 23 (LP form) | the three LP inputs (binders of SquarePositiveDerived.lean:40) | FirstPass/LPBridge/LQGMeasureSquarePositive.lean | READY |
| LQGMetric | support: `SatisfiesLQGMetricAxioms` :47, `IsLQGMetric` :73, `LQGMetricFieldAxioms` :117 | support | none | M5b | READY |
| LQGMetricMeasurable | support: deterministic continuity of the internal metric (`IsEuclideanLengthMetric.continuousAt_internalMetric_self` :329) | support (32) | none | FirstPass/LPBridge/LQGMetricMeasurable.lean | READY |
| LQGMetricMeasurable2 | `lqgMetricPointwiseAEMeasurable_lp` :85 (def :63); `lqgInternalDiamInnerMeasurable_lp` :116 (def :72) | 32; PointwiseAE (no table row) | none | FirstPass/LPBridge/LQGMetricMeasurable.lean | READY |
| LQGMetricUniv | `lqgMetricSatisfiesAxiomsUniv` :315 (def `LQGMetricSatisfiesAxiomsUnivLP` :297); `lqgMetricLengthUniv` :346 (def :307) | 42 (length); axioms: see z3 report | none | FirstPass/LPBridge/LQGMetricUniv.lean | READY |
| LQGWeylScaling | `lqgMeasureWeylScaling_lp` :300 (def `LQGMeasureWeylScalingLP` :291) | 5 | none | FirstPass/LPBridge/LQGWeylScaling.lean | READY |
| LengthMetric | support: `curveLength` :34, `pathLength` :39, `internalMetric` :44, `internalDiam` :49, `IsEuclideanLengthMetric` :54 | support (39, 57) | none | M5a, M5b | READY |
| LengthMetricDerived | `weylScaledEuclidean_derived` :1426; `internalMetricClosedEqIInfThickening_derived` :1517 | 57; 39 | `IsEuclideanLengthMetric` (definition, LengthMetric:54) | M5c | READY |
| LiouvilleGraph | def `WholePlaneLQGGraphDimension` :83 (no theorem) | 44 | none | M6 | READY |
| LocalObservation | support: `recenteredRestriction` :26, `normalizedRestriction` :34, `measurable_normalizedRestriction` :46 | support | none | M2 | READY |
| MassFunctional | `lqgMassFunctionalMeasurable_lp` :759 (def `LQGMassFunctionalMeasurableLP` :67) | 21 | none | FirstPass/LPBridge/MassFunctional.lean | READY |
| PhaseTorus | def `PhaseTorusDoublingProductErgodic` :45 (no theorem; unproved) | 9 | none | M2 | READY |
| PlanarGreen | support: `planarNewtonKernel` :30, `IsHarmonicMinorant` :41, `greenFunction` :56 | support | none | M3 | READY |
| PlaneDomainConvexCompact | `isPreconnected_diff_of_convex_compact` :135 | 35 | none | - | READY |
| PlaneTopology | def `TorhorstSimpleLoop` :72 (no theorem) | 36 | none | M3 | READY |
| WeylCompositionOuter | support: `IsEuclideanLengthMetric.weylScaling_nhds` :166, `innerDist` :242, `IsEuclideanLengthMetric.weylScaling_le_iterated` :657 | support (56) | none | - (via WeylCompositionOuter2) | READY |
| WeylCompositionOuter2 | `weylMetricCompositionContinuousOuter_lp` :543 (def `WeylMetricCompositionContinuousOuterLP` :534); `riemann_arc` :293, `weylScaling_innerDist_le_direct` :482 | 56 | none | FirstPass/LPBridge/WeylCompositionOuter.lean | READY |
| WeylInternalClosed | `weylInternalClosed_derived` :38 (helpers imported from LengthMetricDerived) | 26 | none | FirstPass/LPBridge/M5a.lean | READY |
| WeylMassMeasurable | `measurable_lintegral_of_caratheodory` :28 (general measure theory) | support (27) | none | - | READY |
| WeylOffOrigin | `localLQGInsertionWeylOffOrigin_lp` :587 (def :574); `radonUniqueLP` :181 | 11 | none | FirstPass/LPBridge/WeylOffOrigin.lean | READY |
| WeylShiftedMass | `weylShiftedMassMeasurable_lp` :131 (def `WeylShiftedMassMeasurableLP` :40) | 27 (LP form) | none (proved) | FirstPass/LPBridge/WeylShiftedMass.lean | HOLD (condition 2: `lb HarmonicBalls.LPStage.All` not re-run since commit 1bc9a7c5; see move-status notes) |
| WeylSupMeasurable | `aemeasurable_iSup_mem_of_lowerSemicontinuousOn` :43 | 28 | none | - | READY |

**Move status notes** (column `move`; task fp-lpstage-move-status-then-clean-c5-steps, 2026-11-11). READY means the four conditions hold: (1) imported by `All.lean`; (2) `lb HarmonicBalls.LPStage.All` passes; (3) no task other than the owner's edits or owns the module (`tasks/*.md`); (4) imports only Mathlib, `LatticeProb.*` or `HarmonicBalls.LPStage.*`.
- Condition (2): `lb HarmonicBalls.LPStage.All` run at the start of the round: BUILD OK (HarmonicBalls.LPStage.All; log 123123-3580497.log).
- Condition (4) reading: `import Mathlib` is treated as allowed (the LP library is Mathlib-based). Any other import would be HOLD; none of the 54 modules has one.
- Condition (3): z4 (`tasks/z4.md`) only REUSEs `LQGMeasure` and `WeylMassMeasurable`; z6 (`tasks/z6.md`) only reads `LQGMeasureInputs` and cites `FirstPass/LPBridge/LQGMeasureSquarePositive.lean` (same basename, not this module). No task edits them: READY.
- Uncommitted working-tree changes (`git status` M, not made by this task, not named in any `tasks/*.md`): `CameronMartinDerived`, `CameronMartinDerived2`, `CircleAverageApprox`, `CircleAverageApprox2`, `GFF`, `GFFAffineInvariance`, `KolmogorovExtension`, `PhaseTorus`, `PlaneDomainConvexCompact`. Their rows are READY by the four conditions; the lead decides whether the move waits for their commit.
- Round `fp-phase2-event-sub-then-lpindex` (2026-11-11; z4 DONE with these six modules), conditions (1)-(4) as above:
  - `WeylShiftedMass`: HOLD. (1) imported by `All.lean:55`; (3) no task owns it now; (4) imports only Mathlib and `LPStage.*`. Condition (2) is NOT verified: the last `lb HarmonicBalls.LPStage.All` BUILD OK (log `123123-3580497.log`, 13:41:35 UTC) predates commit `1bc9a7c5` (14:53 UTC, "sync mirror docstrings", 47 LPStage files, including its dependencies `GFF`, `LQGMeasure`, `LQGMetric`, `LengthMetric`, `WeylMassMeasurable`, `CircleAverageApprox2`). Re-run `lb HarmonicBalls.LPStage.All`; READY once it passes.
  - `LocalMeasureKernel`, `LocalMeasureKernel2`, `LocalMeasureKernel3`, `LocalMeasureKernel4`, `LocalMeasureKernel5`: HOLD. All committed and clean (b01b9b8c; a130e763 for 2 and 3; 7607f2f4 for 4 and 5). Condition (4) holds for each (Mathlib and `LPStage.*` imports only). Condition (1) fails: none is imported by `All.lean`. Adding them to the umbrella is the lead's decision; condition (2) cannot be checked before that.
  - Ownership: no `tasks/k4*.md` lists any of the six, so none is skipped. `tasks/k5.md` owns `LatticeProb/LQG/LocalMeasureKernel5.lean` in the LP worktree, a different file with the same basename; this does not affect condition (3).
  - LP-MOVE-PLAN.md names only `LocalMeasureKernel{,2}`, as "not moved".
- Cross-check with LP-MOVE-PLAN.md section 1: the same 54 module names as this table; the only difference is the LocalMeasureKernel files above.

Open items (not in `All.lean`):
- z4 `LPStage/LocalMeasureKernel{,2,3,4,5}.lean`: committed by z4 (b01b9b8c, a130e763, 7607f2f4), not imported by `All.lean`; the
  umbrella decision is the lead's.
- Done 2026-11-11: the `LQGMetricMeasurable.lean:5` header now cites row 32 (`LQGInternalDiamInnerMeasurableFrozen`) for the
  support and says that PointwiseAE has no inventory row (row 33 is `LQGMassInnerMeasurableFrozen`).
- Row 50 (`lqgVolumeGrowthAllScalesStmt_of_scaled_lp`, LQGMeasureFullSupport3:386): no FirstPass bridge file yet.
