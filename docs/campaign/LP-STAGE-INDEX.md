# LP staging area: index of `HarmonicBalls/LPStage`

Umbrella: `HarmonicBalls/LPStage/All.lean` imports the 37 committed LPStage modules whose tasks are finished (build with
`lb HarmonicBalls.LPStage.All`). Not yet imported: the z7 LQGMeasureNonatomic* modules and the z3 LQGMeasureFullSupport*
and LQGMeasureSquarePositive modules (their reports are not DONE; see the open items at the end of this file).
Row numbers are those of `docs/campaign/PHASE2-INVENTORY.md` section 2 (the 57 inputs; as in PHASE2-DERIVATION-STATUS.md).
"HB row" = the staged input; "support" = definitions or lemmas used by a staged result, no row of their own.
"Hypotheses": "none" = the main result takes no literature Prop; a definitional predicate (e.g. `IsWholePlaneGFF`) is not counted.
Line numbers are those of the committed files at the time of the row-56 commit.

| LPStage module | main result(s) (file:line) | HB row(s) | hypotheses | LPBridge file |
|---|---|---|---|---|
| BirkhoffErgodic | `ae_tendsto_birkhoffAverage_integral_of_ergodic` :155 (imports LP `Prob.Birkhoff`) | 7 | none | - |
| CameronMartinDerived | support: `localFieldPairings` :36, `wholePlaneGFF_localFieldPairings_map_eq` :93 | support (13, 37) | none | - (via CameronMartinDerived2) |
| CameronMartinDerived2 | `cameronMartinGFFReweighting_derived` :653; `cameronMartinGFFMutualAbsCont_derived` :869 | 37; 13 | none | FirstPass/LPBridge/CameronMartin.lean |
| CircleAverageApprox | support: `circleDensity` :55, circle-density facts :59-75 | support | none | - (via CircleAverageApprox2) |
| CircleAverageApprox2 | `IsWholePlaneGFF.isProbabilityMeasure` :20, `IsWholePlaneGFF.hasGaussianLaw_circle` :26, `ae_tendsto_circleApprox` :927 | support | none | - (via GFFAffineInvariance) |
| GFF | base definitions: `CircleParameter` :42, `IsTestFunction` :46, `wholePlaneCov` :52, `IsAdmissible` :66, `eval` :71, `smear` :77 | none (base) | none | M1, M4, M5b |
| GFFAffineInvariance | `wholePlaneGFFAffineInvariance_lp` :877 (def `WholePlaneGFFAffineInvarianceLP` :868) | 10 | none | FirstPass/LPBridge/GFFAffineInvariance.lean |
| GFFCovSymm | `wholePlaneCovSymm_proved` :486 (`WholePlaneCovSymmStmt`); `exists_isWholePlaneGFF_of_psd` :500 | support (29) | `WholePlaneCovPSDStmt` (B2) remains | - |
| GFFExistence | `exists_isWholePlaneGFF` :612; `kernelMatrix_posSemidef_of_psd` :539; `kolmogorovExtensionStmt_proved` :45 | 29 | B2 `WholePlaneCovPSDStmt` (:54) open; `KolmogorovExtensionStmt` discharged at :45 | - |
| KolmogorovExtension | `exists_isProjectiveLimit_real` :197 (Kolmogorov extension, LP stage) | support (for `KolmogorovExtensionStmt`) | none | - |
| LQGMassInner | `lqgMassInnerMeasurable_of_gff` :33 | 33 | none | FirstPass/LPBridge/LQGMassInner.lean |
| LQGMeasure | support: `lqgQ` :34, `dyadicScale` :38, `lqgApprox` :43, `IsLQGLimit` :49, `IsLQGMeasure` :58 | support | none | M4 |
| LQGMeasureDerived | `lqgMeasureOfProfileMeasurable_lp` :575 (def `LQGMeasureOfProfileMeasurableLP` :31) | 6 | none | FirstPass/LPBridge/LQGMeasureDerived.lean |
| LQGMeasureInputs | LP forms of the Proposed inputs, as definitions: `LQGMeasureExistenceLP` :52, `LQGMeasureCoordChangeLP` :40, `WholePlaneLQGBallMassBoundsLP` :27 (no theorem) | 1; 2; 3 | LP literature Props, defined not proved | - |
| LQGMeasureLocality | conditional `lqgLocality_of_circleLink` :410; defs `LQGLocality` :88, `LQGCircleAverageLink` :99 | 49 (conditional form) | `LQGCircleAverageLink` (:99); discharged by `lqgCircleAverageLink_of_gff` (LQGMeasureLocality2:151) | via LQGMeasureLocality2 bridge |
| LQGMeasureLocality2 | unconditional `lqgLocality_of_gff` :171; `lqgCircleAverageLink_of_gff` :151 | 49 (unconditional) | none beyond `IsWholePlaneGFF` | FirstPass/LPBridge/LQGMeasureLocality.lean |
| LQGMeasureSquare | `aemeasurable_lqgMeasure_borel` :121; `aemeasurable_lqgMeasure_open` :109 | 22 | `LQGLocality` (LP form of row 49 input) | FirstPass/LPBridge/LQGMeasureSquare.lean |
| LQGMetric | support: `SatisfiesLQGMetricAxioms` :47, `IsLQGMetric` :73, `LQGMetricFieldAxioms` :117 | support | none | M5b |
| LQGMetricMeasurable | support: deterministic continuity of the internal metric (`IsEuclideanLengthMetric.continuousAt_internalMetric_self` :329) | support (32) | none | FirstPass/LPBridge/LQGMetricMeasurable.lean |
| LQGMetricMeasurable2 | `lqgMetricPointwiseAEMeasurable_lp` :85 (def :63); `lqgInternalDiamInnerMeasurable_lp` :116 (def :72) | 32; PointwiseAE (no table row) | none | FirstPass/LPBridge/LQGMetricMeasurable.lean |
| LQGMetricUniv | `lqgMetricSatisfiesAxiomsUniv` :315 (def `LQGMetricSatisfiesAxiomsUnivLP` :297); `lqgMetricLengthUniv` :346 (def :307) | 42 (length); axioms: see z3 report | none | FirstPass/LPBridge/LQGMetricUniv.lean |
| LQGWeylScaling | `lqgMeasureWeylScaling_lp` :300 (def `LQGMeasureWeylScalingLP` :291) | 5 | none | FirstPass/LPBridge/LQGWeylScaling.lean |
| LengthMetric | support: `curveLength` :34, `pathLength` :39, `internalMetric` :44, `internalDiam` :49, `IsEuclideanLengthMetric` :54 | support (39, 57) | none | M5a, M5b |
| LengthMetricDerived | `weylScaledEuclidean_derived` :1426; `internalMetricClosedEqIInfThickening_derived` :1517 | 57; 39 | `IsEuclideanLengthMetric` (definition, LengthMetric:54) | M5c |
| LiouvilleGraph | def `WholePlaneLQGGraphDimension` :83 (no theorem) | 44 | none | M6 |
| LocalObservation | support: `recenteredRestriction` :26, `normalizedRestriction` :34, `measurable_normalizedRestriction` :46 | support | none | M2 |
| MassFunctional | `lqgMassFunctionalMeasurable_lp` :759 (def `LQGMassFunctionalMeasurableLP` :67) | 21 | none | FirstPass/LPBridge/MassFunctional.lean |
| PhaseTorus | def `PhaseTorusDoublingProductErgodic` :45 (no theorem; unproved) | 9 | none | M2 |
| PlanarGreen | support: `planarNewtonKernel` :30, `IsHarmonicMinorant` :41, `greenFunction` :56 | support | none | M3 |
| PlaneDomainConvexCompact | `isPreconnected_diff_of_convex_compact` :135 | 35 | none | - |
| PlaneTopology | def `TorhorstSimpleLoop` :72 (no theorem) | 36 | none | M3 |
| WeylCompositionOuter | support: `IsEuclideanLengthMetric.weylScaling_nhds` :166, `innerDist` :242, `IsEuclideanLengthMetric.weylScaling_le_iterated` :657 | support (56) | none | - (via WeylCompositionOuter2) |
| WeylCompositionOuter2 | `weylMetricCompositionContinuousOuter_lp` :543 (def `WeylMetricCompositionContinuousOuterLP` :534); `riemann_arc` :293, `weylScaling_innerDist_le_direct` :482 | 56 | none | FirstPass/LPBridge/WeylCompositionOuter.lean |
| WeylInternalClosed | `weylInternalClosed_derived` :38 (helpers imported from LengthMetricDerived) | 26 | none | FirstPass/LPBridge/M5a.lean |
| WeylMassMeasurable | `measurable_lintegral_of_caratheodory` :28 (general measure theory) | support (27) | none | - |
| WeylOffOrigin | `localLQGInsertionWeylOffOrigin_lp` :587 (def :574); `radonUniqueLP` :181 | 11 | none | FirstPass/LPBridge/WeylOffOrigin.lean |
| WeylSupMeasurable | `aemeasurable_iSup_mem_of_lowerSemicontinuousOn` :43 | 28 | none | - |

Open items (not in `All.lean`):
- z7 LQGMeasureNonatomic* (report IN_PROGRESS) and z3 LQGMeasureFullSupport*, LQGMeasureSquarePositive (report BLOCKED): add when DONE.
- LQGMetricMeasurable.lean:5 header cites "row 33" for the PointwiseAE form; row 33 of the table is `LQGMassInnerMeasurableFrozen`, and no table row names PointwiseAE. Note to be corrected by z7.
