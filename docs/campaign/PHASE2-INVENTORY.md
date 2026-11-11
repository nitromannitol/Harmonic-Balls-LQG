# Phase 2 inventory: first-pass inputs of the counted HB declarations

Owner: z4, task fp-phase2-inventory (lead lh, operator brief 2026-11-10 22:30 UTC, item A). Report only: no Lean file is changed by this document.

Source of truth: the Lean extraction (scratch-z4/Phase2Extract.lean, scratch-z4/Phase2ExtractB.lean; uncommitted; lc OK), not FIRST-PASS-INPUTS.md (Main.lean 1437843, older). Extraction ran on the working tree of this round; HEAD at commit: 457dbb07.

## 0. Method and counts

- Counted declarations: 64 (one per numbered result that has one). Result 2.5 has none: HarmonicBalls/FirstPass/Closure.lean:34 records it as CITED (Draft GreenPotentialHolderStmt, Draft/Section2.lean:190). INVENTORY.tsv has 65 paper-owned rows.
- "Counted" = the declaration named by the lead (top forms, notes/lead-lh-requests.md R14/R15) or else closure_X_Y in HarmonicBalls.Closure. The status script itself was not found on the sandbox, so section 1 lists alternates and flags ambiguity.
- Extraction: for each counted declaration, forallTelescope over its type; for each Prop-typed binder, the head constant and its defining module (Environment.getModuleIdxFor?). Binders of the type only: a hypothesis used in a proof but not stated in the type is not listed.
- Distinct Prop-typed heads: 62. Five are Mathlib/Init (Bornology.IsBounded, Exists, IsConnected, IsOpen, Set.Nonempty; binders of the explicit-G statement closure_10_5) and are not inputs. Remaining: 57 inputs.
- Classes: P = HarmonicBalls.Proposed.* (pending operator source-check); F = module under FirstPass/Frozen/ (FIRST-PASS FROZEN); FO = FirstPass module outside Frozen/ (S11r/Frozen.lean, S11n/MeasureDecoder.lean, S11i/Step8PhysReduction.lean, S11r/LocalMetricReplacement.lean, S11i/Faithful.lean); D = HarmonicBalls.Draft.* (cited statement, or an HB result passed as a hypothesis, category own).
- Categories (operator brief): (a) result of the other paper (IDLA) proved in Lean: none of the 57 inputs; (b) general background (GFF, LQG measure/metric, Cameron-Martin, Green/potential, ergodic, measurability, plane topology): LP candidate; (c) paper-specific (Section 11 decoders, Lemma 8.2 local form, Lemma 10.5/11.10 specific); own = HB-internal result, not literature (flagged in section 4).
- Uses = number of counted declarations whose type takes the input as a binder (of 64).

## 1. Counted declarations (one per numbered result)

| Result | Counted declaration | file:line | result head | Prop binders | Alternates in the ClosureAll env (same result head) / note |
|---|---|---|---|---|---|
| 1.1 | `closure_1_1` | HarmonicBalls/FirstPass/Closure.lean:154 | ExistenceUniquenessHarmonicBallsStmt | 11 | closure_1_1_noWeyl, firstPass_1_1, firstPassMain_1_1 . closure_1_1 variant closure_1_1_noWeyl drops hWeyl; firstPassMain_1_1 is the old Main.lean route. |
| 1.2 | `closure_1_2_paperExponent_of_11_13` | HarmonicBalls/FirstPass/Closure/PaperExponentOf13.lean:54 | Closure.HarmonicBallNoveltyFaithfulStmt | 18 | closure_1_2_faithful, closure_1_2_faithful_canonical, closure_1_2_faithful_canonical_of_11_13, closure_1_2_faithful_canonical_of_11_13_clean, closure_1_2_faithful_noWeyl, closure_1_2_paperExponent (+2) . LEAD-NAMED top form (PaperExponentOf13.lean:54). Other 1.2 forms: closure_1_2 (Draft novelty), closure_1_2_canonical_of_11_13, closure_1_2_faithful_canonical_of_11_13, firstPass_1_2_faithful_v1. |
| 1.3 | `closure_1_3` | HarmonicBalls/FirstPass/Closure.lean:221 | HarmonicBallLocalSetStmt | 12 | closure_1_3_noWeyl, firstPass_1_3, firstPassMain_1_3 |
| 2.3 | `closure_2_3` | HarmonicBalls/FirstPass/Closure.lean:113 | GreenFunctionBallStmt | 0 | firstPass_2_3 |
| 3.1 | `closure_3_1` | HarmonicBalls/FirstPass/Closure.lean:134 | LeastSupersolutionMemStmt | 6 | firstPass_3_1 |
| 3.2 | `closure_3_2` | HarmonicBalls/FirstPass/Closure.lean:137 | ClusterOpenLaplacianStmt | 6 | firstPass_3_2 |
| 3.3 | `closure_3_3` | HarmonicBalls/FirstPass/Closure.lean:140 | ClusterMonotoneStmt | 6 | firstPass_3_3 |
| 3.4 | `closure_3_4` | HarmonicBalls/FirstPass/Closure.lean:143 | ClusterConservationOfMassStmt | 6 | firstPass_3_4 |
| 3.5 | `closure_3_5` | HarmonicBalls/FirstPass/Closure.lean:146 | ClusterCompatibilityStmt | 6 | firstPass_3_5 |
| 4.1 | `closure_4_1` | HarmonicBalls/FirstPass/Closure/SecA45.lean:73 | ClusterLowerBoundStmt | 5 | firstPass_4_1 |
| 4.2 | `closure_4_2` | HarmonicBalls/FirstPass/Closure/SecA45.lean:76 | LeastSupersolutionHolderStmt | 5 | firstPass_4_2 |
| 4.3 | `closure_4_3` | HarmonicBalls/FirstPass/Closure/SecA45.lean:79 | ClusterSubharmonicBallStmt | 5 | firstPass_4_3 |
| 5.1 | `closure_5_1` | HarmonicBalls/FirstPass/Closure/SecA45.lean:116 | ClusterUpperBoundStmt | 3 | firstPass_5_1 |
| 5.2 | `closure_5_2` | HarmonicBalls/FirstPass/Closure/SecA45.lean:163 | ClusterContinuityStmt | 10 | closure_5_2_noWeyl, firstPass_5_2 |
| 5.3 | `closure_5_3` | HarmonicBalls/FirstPass/Closure/SecA45.lean:182 | ClusterBoundaryMeasureZeroStmt | 10 | closure_5_3_noWeyl, firstPass_5_3 |
| 5.4 | `closure_5_4` | HarmonicBalls/FirstPass/Closure/SecA45.lean:201 | RegularizedClusterHarmonicBallsStmt | 10 | closure_5_4_noWeyl, firstPass_5_4 |
| 5.5 | `closure_5_5` | HarmonicBalls/FirstPass/Closure/SecA45.lean:220 | ExistenceHarmonicBallsStmt | 10 | closure_5_5_noWeyl, firstPass_5_5 . closure_5_5_noWeyl (Sec8Weyl.lean:107) drops hWeyl; firstPass_5_5 has the same statement. |
| 5.6 | `closure_5_6` | HarmonicBalls/FirstPass/Closure/SecA45.lean:127 | UniquenessHarmonicBallsStmt | 3 | firstPass_5_6 |
| 5.7 | `closure_5_7` | HarmonicBalls/FirstPass/Closure/SecA45.lean:139 | ClusterScaleInvarianceStmt | 3 | firstPass_5_7 |
| 5.8 | `closure_5_8` | HarmonicBalls/FirstPass/Closure/SecA45.lean:150 | ClusterStrongCompatibilityStmt | 3 | firstPass_5_8 |
| 6.1 | `closure_6_1` | HarmonicBalls/FirstPass/Closure/Sec6.lean:37 | HarnackTypeEstimateStmt | 3 | firstPass_6_1 |
| 6.2 | `closure_6_2` | HarmonicBalls/FirstPass/Closure/Sec6.lean:41 | HarnackTypeComponentStmt | 3 | firstPass_6_2 |
| 6.3 | `closure_6_3` | HarmonicBalls/FirstPass/Closure/Sec6.lean:45 | ManyGoodAnnuliStmt | 3 | firstPass_6_3 |
| 6.4 | `closure_6_4` | HarmonicBalls/FirstPass/Closure/Sec6.lean:49 | GoodAnnulusProbabilityStmt | 3 | firstPass_6_4 |
| 6.6 | `closure_6_6` | HarmonicBalls/FirstPass/Closure/Sec6.lean:53 | ManyVeryGoodAnnuliStmt | 3 | firstPass_6_6 |
| 6.7 | `closure_6_7` | HarmonicBalls/FirstPass/Closure/Sec6.lean:57 | VeryGoodAnnulusProbabilityStmt | 3 | firstPass_6_7 |
| 6.8 | `closure_6_8` | HarmonicBalls/FirstPass/Closure/Sec6.lean:62 | AnnulusMassBoundByOdometerStmt | 3 | firstPass_6_8 |
| 6.9 | `closure_6_9` | HarmonicBalls/FirstPass/Closure/Sec6.lean:67 | OdometerHarmonicMeasureBoundStmt | 3 | firstPass_6_9 |
| 6.10 | `closure_6_10` | HarmonicBalls/FirstPass/Closure/Sec6.lean:72 | OdometerBoundByAnnulusMassStmt | 3 | firstPass_6_10 |
| 6.11 | `closure_6_11` | HarmonicBalls/FirstPass/Closure/Sec6.lean:77 | VeryGoodAnnulusHarnackTypeStmt | 3 | firstPass_6_11 |
| 6.12 | `closure_6_12` | HarmonicBalls/FirstPass/Closure/Sec6.lean:82 | ShellDecompositionStmt | 3 | firstPass_6_12 |
| 6.13 | `closure_6_13` | HarmonicBalls/FirstPass/Closure/Sec6.lean:87 | LowMassSmallOdometerStmt | 3 | firstPass_6_13 |
| 7.1 | `closure_7_1` | HarmonicBalls/FirstPass/Closure/Sec78910.lean:88 | ClusterUpperBoundPolyHighProbStmt | 3 | firstPass_7_1 |
| 7.2 | `closure_7_2` | HarmonicBalls/FirstPass/Closure/Sec78910.lean:100 | ClusterTimeContinuityStmt | 11 | closure_7_2_noWeyl, firstPass_7_2 |
| 8.1 | `closure_8_1` | HarmonicBalls/FirstPass/Closure/Sec78910.lean:126 | BoundaryMeasureZeroOfCompactClusterStmt | 11 | closure_8_1_noWeyl, firstPass_8_1 |
| 8.2 | `firstPass_8_2_S8d_noWeyl` | HarmonicBalls/FirstPass/S8dNoWeyl.lean:26 | TypicalPointManyGoodScalesStmt | 10 | closure_8_2, closure_8_2_noWeyl, firstPass_8_2 . Lead R15 decision (a): firstPass_8_2_S8d_noWeyl. closure_8_2 uses hWeyl. firstPass_8_2 is declared twice (S8c.lean:30, S8d.lean:32), a name clash. |
| 8.3 | `closure_8_3` | HarmonicBalls/FirstPass/Closure/Sec78910.lean:150 | OriginManyGoodScalesStmt | 6 | firstPass_8_3 |
| 9.2 | `closure_9_2` | HarmonicBalls/FirstPass/Closure/Sec78910.lean:170 | S9c.SubharmonicBallUniquenessC51Stmt | 11 | closure_9_2_noWeyl, firstPass_9_2_corrected . AMBIGUOUS NAME: firstPass_9_2_corrected at S9c.lean:119 (C51 form, in the closure env) and at S2S3S4S9SA.lean:124 (weak form, not in the env). Counted: closure_9_2 (same C51 statement). |
| 9.3 | `closure_9_3` | HarmonicBalls/FirstPass/Closure/Sec78910.lean:194 | HarmonicBallBoundarySubsetStmt | 6 | firstPass_9_3 |
| 9.4 | `closure_9_4` | HarmonicBalls/FirstPass/Closure/Sec78910.lean:212 | RegularOpenEqOfAEEqStmt | 6 | firstPass_9_4 |
| 10.1 | `closure_10_1` | HarmonicBalls/FirstPass/Closure/Sec78910.lean:233 | ClusterBoundedCrossingsStmt | 5 | firstPass_10_1 |
| 10.5 | `firstPass_10_5_corrected` | HarmonicBalls/FirstPass/S1S10/CrossingLemma.lean:38 | And | 6 | closure_10_5 . AMBIGUOUS: firstPass_10_5_corrected (S1S10/CrossingLemma.lean:38; named as counted in lead notes) vs closure_10_5 (Sec78910.lean:254, explicit-G form, result is a conjunction). Counted: firstPass_10_5_corrected. |
| 10.6 | `closure_10_6` | HarmonicBalls/FirstPass/Closure/Sec78910.lean:265 | ComplementComponentBoundarySimpleLoopStmt | 7 | firstPass_10_6 |
| 10.7 | `closure_10_7` | HarmonicBalls/FirstPass/Closure/Sec78910.lean:289 | HarmonicBallComplementBoundaryJordanStmt | 12 | closure_10_7_noWeyl, firstPass_10_7 |
| 11.2 | `closure_11_2` | HarmonicBalls/FirstPass/Closure/Sec11.lean:218 | HarmonicBallNotLipschitzStmt | 14 | closure_11_2_noWeyl, firstPass_11_2 |
| 11.5 | `closure_11_5` | HarmonicBalls/FirstPass/Closure/Sec11.lean:189 | NoConeConditionStmt | 14 | closure_11_5_noWeyl, firstPass_11_5 |
| 11.6 | `closure_11_6` | HarmonicBalls/FirstPass/Closure/Sec11.lean:164 | AnnulusMassBoundByHarmonicChainStmt | 10 | closure_11_6_noWeyl, firstPass_11_6 |
| 11.7 | `closure_11_7` | HarmonicBalls/FirstPass/Closure/Sec11.lean:92 | ManyConeBadScalesStmt | 8 | firstPass_11_7 |
| 11.8 | `closure_11_8` | HarmonicBalls/FirstPass/Closure/Sec11.lean:80 | ConeBadEventProbabilityStmt | 3 | firstPass_11_8 |
| 11.9 | `closure_11_9` | HarmonicBalls/FirstPass/Closure/Sec11.lean:270 | SmallMetricDiameterLargeMassStmt | 16 | firstPass_11_9 |
| 11.10 | `closure_11_10` | HarmonicBalls/FirstPass/Closure/Sec11.lean:113 | SmallMetricDiameterLargeMassSquareStmt | 11 | firstPass_11_10 |
| 11.11 | `closure_11_11_paperExponent_of_11_13` | HarmonicBalls/FirstPass/Closure/PaperExponentOf13.lean:30 | HarmonicBallNotMetricBallCanonicalStmt | 12 | closure_11_11_canonical, closure_11_11_canonical_of_11_13, closure_11_11_paperExponent, firstPass_11_11_canonical, firstPass_11_11_faithful . LEAD-NAMED top form (PaperExponentOf13.lean:30). Alternates: closure_11_11 (Sec11.lean:247), closure_11_11_noWeyl, closure_11_11_canonical_of_11_13, closure_11_11_paperExponent. |
| 11.12 | `firstPass_11_12_final` | HarmonicBalls/FirstPass/S11m/Final11_12.lean:131 | CorrectedLemma11_12Stmt | 21 | closure_11_12, firstPass_11_12_corrected, firstPass_11_12_corrected_of_inputs, firstPass_11_12_of_inputs . LEAD-NAMED top form (S11m/Final11_12.lean:131). Same statement as closure_11_12 (Sec11.lean:357) and firstPass_11_12_corrected; closure_11_12_clean has CorrectedLemma11_12CleanStmt. |
| 11.13 | `firstPass_11_13_closed` | HarmonicBalls/FirstPass/S11i/Final11_13Close.lean:37 | CorrectedLemma11_13CanonicalStmt | 40 | closure_11_13_canonical, closure_11_13_paperExponent, firstPass_11_13_canonical . LEAD-NAMED (S11i/Final11_13Close.lean:37). NOT in the ClosureAll import closure (env lookup MISSING; imported only by S11i/Step8CalibrationClose.lean). Inputs read by a separate extraction. Alternates in closure: closure_11_13 (CorrectedLemma11_13Stmt), closure_11_13_canonical. |
| 11.14 | `closure_11_14` | HarmonicBalls/FirstPass/Closure/Sec11.lean:139 | PinchEventMetricBallConsequenceStmt | 1 | firstPass_11_14 |
| 11.15 | `closure_11_15` | HarmonicBalls/FirstPass/Closure/Sec11.lean:147 | PinchFirstEventFaithfulStmt | 5 | firstPass_11_15_corrected . AMBIGUOUS: closure_11_15 (Sec11.lean:147) and firstPass_11_15_corrected (S11j/FieldAssembly11_15.lean:276) have the same statement. Counted: closure_11_15. |
| 11.16 | `closure_11_16` | HarmonicBalls/FirstPass/Closure/Sec11.lean:289 | PinchSecondEventFaithfulStmt | 26 | firstPass_11_16_corrected, firstPass_11_16_corrected_of_event, firstPass_11_16_corrected_of_exterior, firstPass_11_16_corrected_of_frozen, firstPass_11_16_corrected_of_parts, firstPass_11_16_corrected_of_steps (+1) . closure_11_16 (Sec11.lean:289); firstPass_11_16_corrected and six *_corrected_of_* variants have the same statement. Counted: closure_11_16. |
| 11.17 | `closure_11_17` | HarmonicBalls/FirstPass/Closure/Sec11.lean:320 | PinchThirdEventFaithfulStmt | 27 | firstPass_11_17_corrected, firstPass_11_17_of_11_16 . closure_11_17 (Sec11.lean:320); firstPass_11_17_corrected and firstPass_11_17_of_11_16 have the same statement. Counted: closure_11_17. |
| A.1 | `closure_A_1` | HarmonicBalls/FirstPass/Closure/SecA45.lean:37 | ObstacleLeastSuperharmonicMajorantStmt | 0 | firstPass_A_1 |
| A.2 | `closure_A_2` | HarmonicBalls/FirstPass/Closure/SecA45.lean:40 | ObstacleNonCoincidenceHarmonicStmt | 0 | firstPass_A_2 |
| A.3 | `closure_A_3` | HarmonicBalls/FirstPass/Closure/SecA45.lean:43 | ObstacleMonotoneStmt | 0 | firstPass_A_3 |
| A.4 | `closure_A_4` | HarmonicBalls/FirstPass/Closure/SecA45.lean:46 | ObstacleOdometerZeroBoundaryStmt | 0 | firstPass_A_4 |
| A.5 | `closure_A_5` | HarmonicBalls/FirstPass/Closure/SecA45.lean:49 | ObstacleConservationOfMassStmt | 0 | firstPass_A_5 |
| A.6 | `closure_A_6` | HarmonicBalls/FirstPass/Closure/SecA45.lean:52 | ObstacleCompatibilityStmt | 0 | firstPass_A_6 |

## 2. Inputs (one row per distinct Prop-typed input; 57 rows)

| # | Input (head) | file:line | class | cat | uses | used by (results) | content (one line) | literature source (docstring) | truth status (docstring) | LP match (b) |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `LQGMeasureExistence` | HarmonicBalls/Proposed/LQG.lean:68 | P | b | 52 | 1.1, 1.2, 1.3, 10.1, 10.6, 10.7, 11.11, 11.12, 11.13, 11.16 (+42) | Existence of the gamma-LQG measure mu_h, gamma in (0,2), alpha0 < Q (eq:measure-lim) | paper l.396; Duplantier-Sheffield arXiv:0808.1560v2 Prop 1.1; Berestycki-Powell arXiv:2404.16642v2 Thm 2.1 | PENDING operator source-check | partial: S2 items 3-4 (GMC lower tail, approximations); no existence theorem |
| 2 | `LQGMeasureCoordChange` | HarmonicBalls/Proposed/LQG.lean:116 | P | b | 49 | 1.1, 1.2, 1.3, 10.1, 10.6, 10.7, 11.11, 11.12, 11.2, 11.5 (+39) | Fact 2.1 IV: mu_h covariance under a.s. complex affine maps | paper l.412; Duplantier-Sheffield 2011 Prop 2.1; Sheffield-Wang 2016 | PENDING operator source-check | none: S2 "coordinate-change identity" absent |
| 3 | `WholePlaneLQGBallMassBounds` | HarmonicBalls/Proposed/LQG.lean:154 | P | b | 49 | 1.1, 1.2, 1.3, 10.1, 10.6, 10.7, 11.11, 11.12, 11.13, 11.2 (+39) | LQG mass of Euclidean balls for the normalised whole-plane GFF | Ding-Gwynne arXiv:1807.01072 Lemma 3.8 p.25 | PENDING operator source-check | none listed (S2, S3 do not cover ball-mass bounds) |
| 4 | `LQGMeasureNonatomic` | HarmonicBalls/Proposed/LQG.lean:77 | P | b | 32 | 1.1, 1.2, 1.3, 10.1, 10.6, 10.7, 11.11, 11.16, 11.17, 11.2 (+22) | Fact 2.1 I: mu_h is non-atomic | paper l.404, 418; Berestycki-Powell arXiv:2404.16642v2 p.62 | PENDING operator source-check F4 | partial: S2 item 1 ae_measure_singleton_eq_zero (IsGFFCircleAverage setting) |
| 5 | `LQGMeasureWeylScaling` | HarmonicBalls/Proposed/LQG.lean:95 | P | b | 32 | 1.1, 1.2, 1.3, 10.1, 10.6, 10.7, 11.11, 11.12, 11.13, 11.16 (+22) | Fact 2.1 III: e^{gamma f} mu_h = mu_{h+f} for continuous f | paper l.406, 418 ("immediate from the definition") | PENDING operator source-check | none: S2 has no Weyl identity for GMC; S3 weylScale is metric-only |
| 6 | `LQGMeasureOfProfileMeasurableFrozen` | HarmonicBalls/FirstPass/Frozen/S8d.lean:33 | F | b | 18 | 1.1, 1.2, 1.3, 10.7, 11.11, 11.13, 11.2, 11.5, 11.6, 11.7 (+8) | Profile-level measurability of the gamma-LQG measure from circle-average profile | Duplantier-Sheffield arXiv:0808.1560 Prop 1.1 (locator pending) | Truth check TRUE (ChatGPT turn 2, 02:58 UTC) | partial: S2 item 6 exists_measurable_version (generic) |
| 7 | `BirkhoffPointwiseErgodic` | HarmonicBalls/FirstPass/Frozen/S8c.lean:100 | F | b | 17 | 1.1, 1.2, 1.3, 10.7, 11.11, 11.13, 11.2, 11.5, 11.6, 5.2 (+7) | Birkhoff pointwise ergodic theorem for bounded measurable f, ergodic T | standard (Birkhoff) | not stated in docstring | partial: S9 item 1 ae_tendsto_bAvg (Prob/Birkhoff.lean:671); ergodic limit to check |
| 8 | `LocalRootedFieldMeasureDomination` | HarmonicBalls/FirstPass/Frozen/S8c.lean:55 | F | b | 16 | 1.1, 1.2, 1.3, 10.7, 11.11, 11.2, 11.5, 11.6, 5.2, 5.3 (+6) | Local rooted field-measure identification (ball avoiding 0), Lemma 8.2 local form | Duplantier-Miller-Sheffield arXiv:1409.7055 (rooted measures) | restated (owner n4); verdict not in docstring | none listed |
| 9 | `PhaseTorusDoublingProductErgodicFrozen` | HarmonicBalls/FirstPass/Frozen/S8d.lean:58 | F | b | 16 | 1.1, 1.2, 1.3, 10.7, 11.11, 11.2, 11.5, 11.6, 5.2, 5.3 (+6) | Product ergodicity of the doubling map with an ergodic measure-preserving map | standard; Thm 1.27, Prop 1.5 (cited in docstring) | Truth check TRUE (ChatGPT turn 2, 02:58 UTC) | partial: S9 item 7 Ergodic (Mathlib); no product theorem |
| 10 | `WholePlaneGFFAffineInvariance` | HarmonicBalls/Proposed/LQG.lean:53 | P | b | 16 | 1.1, 1.2, 1.3, 10.6, 10.7, 3.1, 3.2, 3.3, 3.4, 3.5 (+6) | Affine invariance of the whole-plane GFF modulo additive constant (eq:gff-scaling) | Gwynne-Holden-Sun arXiv:1910.04713v2 S3.2.2; paper l.367 | PENDING operator source-check | none listed (S1 has no affine invariance) |
| 11 | `LocalLQGInsertionWeylOffOrigin` | HarmonicBalls/FirstPass/Frozen/S8c.lean:85 | F | b | 13 | 1.1, 1.3, 10.7, 11.2, 11.5, 11.6, 5.2, 5.3, 5.4, 5.5 (+3) | Weyl change of variables for the LQG insertion off the origin (Lemma 8.2) | Duplantier-Sheffield; Duplantier-Miller-Sheffield arXiv:1409.7055; paper Lemma 8.2 | RETIRED: derived as localLQGInsertionWeylOffOrigin_derived (S8c/WeylOffOriginDerived.lean:88); truth TRUE (chat 219) F2 | n/a (proved in HB) |
| 12 | `LQGMetricFieldAxiomsUnivFrozen` | HarmonicBalls/FirstPass/Frozen/S11j.lean:155 | F | b | 10 | 1.2, 11.10, 11.11, 11.12, 11.13, 11.14, 11.15, 11.16, 11.17, 11.9 | Universal wrapper of LQGMetricFieldAxioms (LQG metric axioms) | Gwynne arXiv:2208.11795; Gwynne-Miller arXiv:1905.00383 pp.6,8 | PENDING operator source-check (universal wrapper); truth TRUE (00:28 UTC) | partial: S3 item 1 IsStrongLQGMetric (fields) |
| 13 | `CameronMartinGFFMutualAbsCont` | HarmonicBalls/FirstPass/Frozen/S11d.lean:74 | F | b | 6 | 11.12, 11.13, 11.15, 11.16, 11.17, 11.9 | Cameron-Martin quasi-invariance of the whole-plane GFF on distribution-level events | Miller-Sheffield, Imaginary Geometry, Prop 2.9 | UNCLEAR (19:20 UTC: unrestricted sigma-algebra) | partial: S1 items 6-7 (finite tilt; cmDensity) |
| 14 | `LQGInternalMetricWeylAeMeasurableFrozen` | HarmonicBalls/FirstPass/Frozen/S11d.lean:130 | F | b | 6 | 11.12, 11.13, 11.15, 11.16, 11.17, 11.9 | Measurability of h -> D_h for the Weyl-scaled internal metric | Gwynne-Miller 2021 S1; Gwynne arXiv:2208.11795 p.9 | DERIVED INTERFACE (chat 179 Pro audit); no independent verdict | partial: S3 WeylLQG (distance identities, no measurability) |
| 15 | `LocalLQGDecoderCommonFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:388 | F | c | 6 | 1.2, 11.12, 11.13, 11.2, 11.5, 11.7 | Exact common local decoder for the LQG measure (Section 11 locality) | Duplantier-Sheffield arXiv:0808.1560v2 Prop 1.1, Prop 3.1 | DERIVED INTERFACE; TRUE (ChatGPT 2026-11-09) | - |
| 16 | `WeylScalingCompositionFrozen` | HarmonicBalls/FirstPass/Frozen/S11d.lean:91 | F | b | 6 | 11.12, 11.13, 11.15, 11.16, 11.17, 11.9 | Composition of Weyl scaling with the log-singular extension | Gwynne-Miller 2021 pp.6,8; Gwynne-Pfeffer-Sun 2020 p.9 | DERIVED INTERFACE; truth TRUE (ChatGPT 02:49 UTC) | partial: S3 weylScale (metric side only) |
| 17 | `CameronMartinEventTransferFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:149 | F | b | 5 | 11.10, 11.13, 11.16, 11.17, 11.9 | Cameron-Martin transfer of a measurable shifted event | Sheffield arXiv:1302.4738v2 Prop 2.9 (IG4); Lemma 11.10 | FIRST-PASS FROZEN; 19:20 UTC: shifted event must be measurable (check queued) | partial: S1 item 6 (finite tilt only) |
| 18 | `ConnectedSquareUnionDiamFiniteFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:91 | F | b | 5 | 11.10, 11.13, 11.16, 11.17, 11.9 | Finite LQG-metric diameter of a compact connected finite union of closed rectangles | Gwynne-Pfeffer-Sun arXiv:1905.00380v2 Prop 3.10 p.34 | Truth check TRUE (ChatGPT 02:49 UTC) | none listed (S3 has axioms, not diameter bounds) |
| 19 | `DyadicCellDiamSmallFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:67 | F | c | 5 | 11.10, 11.13, 11.16, 11.17, 11.9 | Small internal diameter of enlarged dyadic cells at one level (Lemma 11.10 scope) | Gwynne-Pfeffer-Sun arXiv:1905.00380v2 Prop 3.10 pp.34,45 | attribution note (23:32 UTC audit); no verdict | - |
| 20 | `GreenPotentialHolderStmt` | HarmonicBalls/Draft/Section2.lean:190 | D | b | 5 | 11.12, 11.13, 11.16, 11.17, 8.3 | Green-potential Holder clause of Prop 2.5 (a.s., all smooth O, f in L-infinity) | paper Prop 2.5; Berestycki 2015 Thm 1 (cited; flag F5) | FLAG: docstring says the cited sources do not cover the scope needed F5 | none: S5 keyword grep for Holder finds no match |
| 21 | `LQGMassFunctionalMeasurableFrozen` | HarmonicBalls/FirstPass/Frozen/S11d.lean:155 | F | b | 5 | 11.12, 11.13, 11.16, 11.17, 11.9 | Measurable functional for the LQG mass of a closed set | Duplantier-Sheffield 2011; Gwynne arXiv:2208.11795 Fact 2.1 | DERIVED INTERFACE; no verdict | partial: S2 items 1-5 (GMC facts, IsGFFCircleAverage) |
| 22 | `LQGMeasureSquareMeasurableFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:117 | F | b | 5 | 11.10, 11.13, 11.16, 11.17, 11.9 | omega -> mu_h(S) measurable for a closed dyadic square S | paper Fact 2.1 II l.407 (locality) | FIRST-PASS FROZEN (operator ruling n1, 2026-11-09) | partial: S2 item 5 (measurable circle averages) |
| 23 | `LQGMeasureSquarePositiveFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:130 | F | b | 5 | 11.10, 11.13, 11.16, 11.17, 11.9 | The LQG area measure charges every closed dyadic square a.s. | Duplantier-Sheffield arXiv:1305.6221v1 Thm 2.12 p.11 | FIRST-PASS FROZEN; no ChatGPT verdict in docstring | partial: S2 item 1 (non-atomicity only) |
| 24 | `LQGMetricContinuousShiftFactI` | HarmonicBalls/FirstPass/Frozen/S11d.lean:34 | F | b | 5 | 11.10, 11.13, 11.16, 11.17, 11.9 | Fact 2.2 I: Weyl-scaled metric finite under continuous shift of the field | paper Fact 2.2 I | FIRST-PASS FROZEN; no verdict | partial: S3 item 3 ae_dist_addConst |
| 25 | `LQGMetricSupMeasurableFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:105 | F | b | 5 | 11.10, 11.13, 11.16, 11.17, 11.9 | Field-level measurability of the internal sup of the LQG metric over a finite union | paper Fact 2.2 setting; Lemma 11.10 | FIRST-PASS FROZEN (operator ruling n1, wave 4) | none (metric measurability) |
| 26 | `WeylInternalClosedFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:180 | F | b | 5 | 11.10, 11.13, 11.16, 11.17, 11.9 | Closed-set Weyl comparison for internal metrics (Weyl scaling of the LQG metric) | Gwynne-Miller arXiv:1905.00383v3 pp.5,6 | FIRST-PASS FROZEN (operator ruling 18:35 UTC) | partial: S3 item 5 ae_internal_addFun_of_eq_const |
| 27 | `WeylShiftedMassMeasurableFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:233 | F | b | 5 | 11.10, 11.13, 11.16, 11.17, 11.9 | AE-measurability of the LQG mass of Weyl-shifted sets | paper Prop 1.1 / Fact 2 (measurability of mu_h) | FIRST-PASS FROZEN (operator ruling 19:45 UTC; truth check queued) | none |
| 28 | `WeylShiftedSupMeasurableFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:217 | F | b | 5 | 11.10, 11.13, 11.16, 11.17, 11.9 | AE-measurability of the internal sup of the Weyl-shifted metric | paper Fact 2 (measurability); Gwynne-Miller | FIRST-PASS FROZEN (operator ruling 19:45 UTC; truth check queued) | none |
| 29 | `WholePlaneGFFExistsFrozen` | HarmonicBalls/FirstPass/S11r/Frozen.lean:39 | FO | b | 5 | 11.12, 11.13, 11.15, 11.16, 11.17 | Existence of a whole-plane GFF with the stated normalisation | Miller-Sheffield; Sheffield (docstring "Sources") | Truth check TRUE (ChatGPT 01:17 UTC) | partial/absent: S1 unconditional construction not located |
| 30 | `CameronMartinLocallyLipschitzShiftAbsCont` | HarmonicBalls/FirstPass/Frozen/S11c.lean:414 | F | b | 4 | 1.2, 11.2, 11.5, 11.7 | Cameron-Martin shift: absolute continuity for locally Lipschitz shifts | Sheffield, Imaginary Geometry (G2 option A) | FIRST-PASS FROZEN; TRUE (ChatGPT 2026-11-09, G2) | partial: S1 item 7 (zero-boundary CM map) |
| 31 | `DomainMarkovConditionalPositiveFrozen` | HarmonicBalls/FirstPass/Frozen/S11k.lean:45 | F | b | 4 | 11.12, 11.13, 11.16, 11.17 | Domain Markov property: conditional positivity (normalisation-aware) | GFF Markov property (cf. LMLem2_1) | DERIVED INTERFACE; truth TRUE (operator check) | partial: S1 item 8 lmLem2_1 (Blueprint Prop unread) |
| 32 | `LQGInternalDiamInnerMeasurableFrozen` | HarmonicBalls/FirstPass/Frozen/S11k.lean:89 | F | b | 4 | 11.12, 11.13, 11.16, 11.17 | Measurability of the inner internal diameter of an LQG-metric set | Fact 2.2 I-II, p. 9 (HB Fact 2 source) | DERIVED INTERFACE; no verdict | none |
| 33 | `LQGMassInnerMeasurableFrozen` | HarmonicBalls/FirstPass/Frozen/S11k.lean:66 | F | b | 4 | 11.12, 11.13, 11.16, 11.17 | Measurability of the inner LQG mass of a set | Fact 2.1 II, p. 9 (HB Fact 2 source) | DERIVED INTERFACE; no verdict | none |
| 34 | `LocalCampbellMarkedRestrictionFrozen` | HarmonicBalls/FirstPass/Frozen/S11c.lean:268 | F | b | 4 | 1.2, 11.2, 11.5, 11.7 | Local rooted-field (Campbell-Palm) absolute continuity of the LQG measure | Duplantier-Miller-Sheffield arXiv:1409.7055 | FIRST-PASS FROZEN; no verdict | none listed |
| 35 | `PlaneDomainMinusConvexCompactPreconnectedFrozen` | HarmonicBalls/FirstPass/Frozen/S11d.lean:26 | F | b | 4 | 11.13, 11.16, 11.17, 11.9 | Plane topology: connected open minus compact convex set is connected (Cech H^1) | Alexander duality in S^2; standard (locator pending) | standard; no verdict | not in catalog (plane topology) |
| 36 | `TorhorstSimpleLoopFrozen` | HarmonicBalls/FirstPass/Frozen/S1S10.lean:21 | F | b | 4 | 1.2, 10.5, 10.6, 10.7 | Torhorst theorem for continua, printed form used in corrected Lemma 10.5 | Torhorst (1931); Jolivet-Loridant-Luo | not stated in docstring (see C48) | not in catalog |
| 37 | `CameronMartinGFFReweighting` | HarmonicBalls/FirstPass/Frozen/S11aj.lean:33 | F | b | 2 | 11.12, 11.13 | Cameron-Martin Radon-Nikodym reweighting identity for the GFF | Miller-Sheffield IG; chat 179 audit l.197 | DERIVED INTERFACE; truth TRUE exactly as typed | partial: S1 item 6 (finite tilt) |
| 38 | `CorrectedLemma11_13CanonicalStmt` | HarmonicBalls/FirstPass/S11i/Faithful.lean:102 | D | own | 2 | 1.2, 11.11 | HB result 11.13 in canonical form (xi = lqgXi gamma), used as h13 | paper Lemma 11.13 (own result) | HB result, closed by firstPass_11_13_closed (not in ClosureAll closure) F3 | - |
| 39 | `InternalMetricClosedEqIInfThickeningFrozen` | HarmonicBalls/FirstPass/Frozen/S11g.lean:132 | F | b | 2 | 11.16, 11.17 | Deterministic metric geometry: closed-set exhaustion of the internal metric | none needed (deterministic, proved) | Truth check TRUE (ChatGPT 00:12 UTC) | none listed |
| 40 | `LQGMeasureFullSupportStmt` | HarmonicBalls/Draft/Section2.lean:109 | D | b | 2 | 11.13, 8.2 | Input I1: mu_h(U) > 0 for every nonempty open U, a.s. | GRAPH.md input I1 (no literature in docstring) | not stated: FLAG F5 (no source) F5 | partial: S2 item 1 (non-atomic only) |
| 41 | `LQGMeasureNonatomicAll` | HarmonicBalls/FirstPass/S11n/MeasureDecoder.lean:39 | FO | b | 2 | 11.12, 11.13 | Universal (forall-reordered) form of Proposed LQGMeasureNonatomic, same body | paper Fact 2.1 I | TRUE as quantified with GFF guard (flag F4) F4 | partial: S2 item 1 |
| 42 | `LQGMetricLengthUnivFrozen` | HarmonicBalls/FirstPass/Frozen/S11j.lean:133 | F | b | 2 | 11.12, 11.13 | Universal wrapper: the LQG metric is a length space (a.s.) | Gwynne arXiv:2208.11795; Gwynne-Miller arXiv:1905.00383 pp.6,8 | FIRST-PASS FROZEN (EXTERNAL; truth TRUE 00:28 UTC; ruling B1) | partial: S3 item 1 length field |
| 43 | `SmallMetricDiameterLargeMassStmt` | HarmonicBalls/Draft/Section11.lean:201 | D | own | 2 | 11.12, 11.13 | HB result 11.9 (Proposition 11.9, prop:mass-diam-gen) | paper Prop 11.9 | HB result: closure_11_9 in ClosureAll F3 | - |
| 44 | `WholePlaneLQGGraphDimension` | HarmonicBalls/Proposed/LQGDimension.lean:19 | P | b | 2 | 1.2, 11.11 | LQG graph-distance exponent (fractal dimension of LQG) | Ding-Gwynne, fractal dimension of LQG (docstring) | PENDING operator source-check | none listed |
| 45 | `CoordChangeAlpha0Stmt` | HarmonicBalls/FirstPass/S11i/Step8PhysReduction.lean:81 | FO | c | 1 | 11.13 | Coordinate change at alpha0 = 0 used in the Step 8 physical reduction | paper Section 11 (Step 8); HB-internal (Step8PhysReduction.lean:81) | not stated in docstring F7 | - |
| 46 | `DMSLemmaA10WholePlaneMarkedSub` | HarmonicBalls/FirstPass/Frozen/S11i.lean:58 | F | b | 1 | 11.13 | Duplantier-Miller-Sheffield Lemma A.10, marked whole-plane sub-measure | DMS Lemma A.10 (arXiv:1409.7055) | Operator ruling 2026-11-10; chat 241 S4 truth PRO | none |
| 47 | `LQGCanonicalDecodersExistStmt` | HarmonicBalls/FirstPass/Frozen/S11n.lean:33 | F | c | 1 | 11.12 | Canonical simultaneous decoders exist (Section 11 locality) | Duplantier-Sheffield; Section 11 decoder | EXTERNAL (operator 00:49 UTC); truth not stated | - |
| 48 | `LQGCanonicalDecodersMeasurableExistStmt` | HarmonicBalls/FirstPass/Frozen/S11n.lean:71 | F | c | 1 | 11.13 | Measurable canonical decoders exist | Section 11 decoder; Duplantier-Sheffield | EXTERNAL; truth TRUE (ChatGPT 00:48 UTC, B1 split) | - |
| 49 | `LQGMeasureLocality` | HarmonicBalls/Proposed/LQG.lean:85 | P | b | 1 | 1.3 | Fact 2.1 II: mu_h(U) is a measurable function of h restricted to U | paper l.405, 418 | PENDING operator source-check | none (locality is a field of IsStrongLQGMetric, S3 only) |
| 50 | `LQGVolumeGrowthAllScalesStmt` | HarmonicBalls/Draft/Section2.lean:122 | D | b | 1 | 11.13 | Input I2: eq:volume-growth holds for mu_h at all scales | GRAPH.md input I2; INVENTORY 2.4 cites Berestycki-Gwynne 2020 Lemma A.1 (adapted) | not stated: FLAG F5 (no printed proof) F5 | partial: S2 items 3, 7 (volume/moment bounds) |
| 51 | `LocalMeasureKernelStmt` | HarmonicBalls/FirstPass/S11r/Frozen.lean:144 | FO | c | 1 | 11.13 | Local measure kernel for whole-measure locality (Section 11) | Section 11 (n1/n2 inputs) | FIRST-PASS FROZEN, EXTERNAL; truth TRUE (ChatGPT chat 148) | - |
| 52 | `LocalMetricReplacementFrozen` | HarmonicBalls/FirstPass/Frozen/S11rMetric.lean:33 | F | c | 1 | 11.13 | Local metric replacement, frozen form (gamma, xi, c1, c2, r1, r2) | Section 11 (Target B2); Frozen/S11rMetric.lean:33 | not stated in docstring F7 | - |
| 53 | `LocalMetricReplacementStmt` | HarmonicBalls/FirstPass/S11r/LocalMetricReplacement.lean:58 | FO | c | 1 | 11.12 | Target B2: local metric replacement | CHATGPT-n3-B1-B2 (Section 11) | FIRST-PASS FROZEN, EXTERNAL; truth not stated in snippet | - |
| 54 | `RootedPhysicalMetricContinuousAtInsertionFrozen` | HarmonicBalls/FirstPass/S11r/Frozen.lean:115 | FO | c | 1 | 11.13 | Physical metric continuity at insertion (rooted) | Dubedat-Falconet-Gwynne-Pfeffer-Sun (docstring) | Truth check TRUE (ChatGPT chat 149) | - |
| 55 | `VeryGoodAnnulusProbabilityStmt` | HarmonicBalls/Draft/Section6.lean:331 | D | own | 1 | 8.2 | HB result 6.7 (very good annuli hit), used as hypothesis of 8.2 | paper Lemma 6.7 | HB result: closure_6_7 in ClosureAll F3 | - |
| 56 | `WeylMetricCompositionContinuousOuterFrozen` | HarmonicBalls/FirstPass/Frozen/S11j.lean:117 | F | b | 1 | 11.13 | Continuity of the Weyl-scaled metric composition in the outer variable | Gwynne-Miller; Gwynne-Pfeffer-Sun (replaces retired Weyl input) | EXTERNAL (operator 23:37 UTC); truth TRUE (00:28 UTC) | partial: S3 item 6 weylScale |
| 57 | `WeylScaledEuclideanFrozen` | HarmonicBalls/FirstPass/Frozen/S11g.lean:146 | F | b | 1 | 11.17 | Deterministic metric geometry: Weyl scaling of a Euclidean length metric is Euclidean | standard; locator pending | Truth check TRUE (ChatGPT 00:28 UTC) | partial: S3 item 7 weylScaleOn_eq_internal |

## 3. (b) candidates for LP, ranked by uses

| Rank | Input | uses | class | LP match (docs/campaign/PHASE2-LP-CATALOG.md, section) |
|---|---|---|---|---|
| 1 | `LQGMeasureExistence` | 52 | P | partial: S2 items 3-4 (GMC lower tail, approximations); no existence theorem |
| 2 | `LQGMeasureCoordChange` | 49 | P | none: S2 "coordinate-change identity" absent |
| 3 | `WholePlaneLQGBallMassBounds` | 49 | P | none listed (S2, S3 do not cover ball-mass bounds) |
| 4 | `LQGMeasureNonatomic` | 32 | P | partial: S2 item 1 ae_measure_singleton_eq_zero (IsGFFCircleAverage setting) |
| 5 | `LQGMeasureWeylScaling` | 32 | P | none: S2 has no Weyl identity for GMC; S3 weylScale is metric-only |
| 6 | `LQGMeasureOfProfileMeasurableFrozen` | 18 | F | partial: S2 item 6 exists_measurable_version (generic) |
| 7 | `BirkhoffPointwiseErgodic` | 17 | F | partial: S9 item 1 ae_tendsto_bAvg (Prob/Birkhoff.lean:671); ergodic limit to check |
| 8 | `LocalRootedFieldMeasureDomination` | 16 | F | none listed |
| 9 | `PhaseTorusDoublingProductErgodicFrozen` | 16 | F | partial: S9 item 7 Ergodic (Mathlib); no product theorem |
| 10 | `WholePlaneGFFAffineInvariance` | 16 | P | none listed (S1 has no affine invariance) |
| 11 | `LocalLQGInsertionWeylOffOrigin` | 13 | F | n/a (proved in HB) |
| 12 | `LQGMetricFieldAxiomsUnivFrozen` | 10 | F | partial: S3 item 1 IsStrongLQGMetric (fields) |
| 13 | `CameronMartinGFFMutualAbsCont` | 6 | F | partial: S1 items 6-7 (finite tilt; cmDensity) |
| 14 | `LQGInternalMetricWeylAeMeasurableFrozen` | 6 | F | partial: S3 WeylLQG (distance identities, no measurability) |
| 15 | `WeylScalingCompositionFrozen` | 6 | F | partial: S3 weylScale (metric side only) |
| 16 | `CameronMartinEventTransferFrozen` | 5 | F | partial: S1 item 6 (finite tilt only) |
| 17 | `ConnectedSquareUnionDiamFiniteFrozen` | 5 | F | none listed (S3 has axioms, not diameter bounds) |
| 18 | `GreenPotentialHolderStmt` | 5 | D | none: S5 keyword grep for Holder finds no match |
| 19 | `LQGMassFunctionalMeasurableFrozen` | 5 | F | partial: S2 items 1-5 (GMC facts, IsGFFCircleAverage) |
| 20 | `LQGMeasureSquareMeasurableFrozen` | 5 | F | partial: S2 item 5 (measurable circle averages) |
| 21 | `LQGMeasureSquarePositiveFrozen` | 5 | F | partial: S2 item 1 (non-atomicity only) |
| 22 | `LQGMetricContinuousShiftFactI` | 5 | F | partial: S3 item 3 ae_dist_addConst |
| 23 | `LQGMetricSupMeasurableFrozen` | 5 | F | none (metric measurability) |
| 24 | `WeylInternalClosedFrozen` | 5 | F | partial: S3 item 5 ae_internal_addFun_of_eq_const |
| 25 | `WeylShiftedMassMeasurableFrozen` | 5 | F | none |
| 26 | `WeylShiftedSupMeasurableFrozen` | 5 | F | none |
| 27 | `WholePlaneGFFExistsFrozen` | 5 | FO | partial/absent: S1 unconditional construction not located |
| 28 | `CameronMartinLocallyLipschitzShiftAbsCont` | 4 | F | partial: S1 item 7 (zero-boundary CM map) |
| 29 | `DomainMarkovConditionalPositiveFrozen` | 4 | F | partial: S1 item 8 lmLem2_1 (Blueprint Prop unread) |
| 30 | `LQGInternalDiamInnerMeasurableFrozen` | 4 | F | none |
| 31 | `LQGMassInnerMeasurableFrozen` | 4 | F | none |
| 32 | `LocalCampbellMarkedRestrictionFrozen` | 4 | F | none listed |
| 33 | `PlaneDomainMinusConvexCompactPreconnectedFrozen` | 4 | F | not in catalog (plane topology) |
| 34 | `TorhorstSimpleLoopFrozen` | 4 | F | not in catalog |
| 35 | `CameronMartinGFFReweighting` | 2 | F | partial: S1 item 6 (finite tilt) |
| 36 | `InternalMetricClosedEqIInfThickeningFrozen` | 2 | F | none listed |
| 37 | `LQGMeasureFullSupportStmt` | 2 | D | partial: S2 item 1 (non-atomic only) |
| 38 | `LQGMeasureNonatomicAll` | 2 | FO | partial: S2 item 1 |
| 39 | `LQGMetricLengthUnivFrozen` | 2 | F | partial: S3 item 1 length field |
| 40 | `WholePlaneLQGGraphDimension` | 2 | P | none listed |
| 41 | `DMSLemmaA10WholePlaneMarkedSub` | 1 | F | none |
| 42 | `LQGMeasureLocality` | 1 | P | none (locality is a field of IsStrongLQGMetric, S3 only) |
| 43 | `LQGVolumeGrowthAllScalesStmt` | 1 | D | partial: S2 items 3, 7 (volume/moment bounds) |
| 44 | `WeylMetricCompositionContinuousOuterFrozen` | 1 | F | partial: S3 item 6 weylScale |
| 45 | `WeylScaledEuclideanFrozen` | 1 | F | partial: S3 item 7 weylScaleOn_eq_internal |


## 4. Flags and open questions (for the lead)

- F1 (11.13 is outside the closure). firstPass_11_13_closed (FirstPass/S11i/Final11_13Close.lean:37) is not in the import closure of FirstPass/ClosureAll.lean (environment lookup: MISSING). The file is imported only by FirstPass/S11i/Step8CalibrationClose.lean. Its binders come from the separate extraction (scratch-z4/out-phase2b.txt). Question: does the status build import this module? If not, result 11.13 is not counted in ClosureAll.
- F2 (retired input still a binder). LocalLQGInsertionWeylOffOrigin (FirstPass/Frozen/S8c.lean:85) is RETIRED, derived as localLQGInsertionWeylOffOrigin_derived (FirstPass/S8c/WeylOffOriginDerived.lean:88), yet 13 counted declarations still take it as a binder (for example 1.1, 1.3, 5.2 to 5.5, 10.7, 11.2). The derived theorem could be passed instead; no mathematics is needed for that rewiring.
- F3 (HB results taken as hypotheses; not literature, category own). VeryGoodAnnulusProbabilityStmt (Draft/Section6.lean:331, result 6.7) is an input of 8.2. SmallMetricDiameterLargeMassStmt (Draft/Section11.lean:201, result 11.9) is an input of 11.12 and 11.13. CorrectedLemma11_13CanonicalStmt (FirstPass/S11i/Faithful.lean:102, result 11.13 canonical) is an input of 1.2 and 11.11. Closures exist for 6.7 (closure_6_7), 11.9 (closure_11_9) and 11.13 canonical (closure_11_13_canonical, Closure/Sec11.lean:400). Check for cycles before replacing these binders by imports.
- F4 (duplicate input). LQGMeasureNonatomicAll (FirstPass/S11n/MeasureDecoder.lean:39; 2 uses) is the forall-reordering of the Proposed LQGMeasureNonatomic (Proposed/LQG.lean:77; 32 uses). The same Prop enters as two binders (the lead flagged this in notes R14).
- F5 (Draft inputs without a literature source). LQGMeasureFullSupportStmt (Draft/Section2.lean:109, input I1) and LQGVolumeGrowthAllScalesStmt (Draft/Section2.lean:122, input I2) cite only GRAPH.md or INVENTORY 2.4 (Berestycki-Gwynne 2020 Lemma A.1, "argument adapted, no printed proof"). GreenPotentialHolderStmt (Draft/Section2.lean:190; 5 uses): its docstring says the quoted results' cited sources do not cover the scope the paper needs. Source check needed; nothing is proposed here.
- F6 (truth status open). Eight Proposed inputs are PENDING operator source-check (Proposed/LQG.lean and LQGDimension.lean). CameronMartinGFFMutualAbsCont (6 uses): truth UNCLEAR (19:20 UTC note, unrestricted sigma-algebra). CameronMartinEventTransferFrozen (5 uses): the shifted event must be measurable (19:20 UTC note). WeylShiftedMassMeasurableFrozen and WeylShiftedSupMeasurableFrozen: truth check queued.
- F7 (hand-located). LocalMetricReplacementFrozen (FirstPass/Frozen/S11rMetric.lean:33) and CoordChangeAlpha0Stmt (FirstPass/S11i/Step8PhysReduction.lean:81) were found by hand because the grep missed their universe suffix. Their docstrings were not read (CoordChangeAlpha0Stmt has none recorded).
- F8 (no category (a) items). None of the 57 inputs is a result of the IDLA paper, by module or by docstring. All are Proposed, Frozen, cited Draft, or HB-internal.
- F9 (65 rows, 64 counted). Result 2.5 has no counted declaration (FirstPass/Closure.lean:34, CITED).
- F10 (status script). Not found on the sandbox (repository, fleet directory, lead notes). Counted names come from the lead notes (R14, R15, top forms) and closure_X_Y. Ambiguous cases are marked in section 1: 1.2, 9.2 (two declarations named firstPass_9_2_corrected), 10.5 (two forms), 11.12, 11.13, 11.15, 11.16, 11.17.
- F11 (LP match). docs/campaign/PHASE2-LP-CATALOG.md exists (199 lines). Sections 1, 2, 3 and 9 were used. "none" means no entry in the catalog, not a proof that LP lacks the statement. GreenPotentialHolderStmt was checked only by a keyword grep of section 5.
