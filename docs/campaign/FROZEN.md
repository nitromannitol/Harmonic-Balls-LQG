# FROZEN pending operator approval
Draft statements of "Harmonic balls in Liouville quantum gravity" (Bou-Rabee, Gwynne; arXiv:2208.11795), frozen at
commit 1d4135b (fixes (1), (2), (3), (5) in 10a56e3; fix (4) in 1d4135b; operator inbox 2026-11-03 04:45, after the
statement check ~/paper-checks/hb/review-S.md and the corrections check review-C.md). Paper: paper/lqg_harmonic_ball-corrected.tex;
corrections [Cn]: ~/paper-fleets/hb/CORRECTIONS-PROPOSED.md (adopted by the operator 04:35: C1-C9, C11-C16, C18-C26; C22 tied to C7).
From now on a frozen Stmt changes only with an operator decision in inbox.md. 72 statements: the 69 numbered results (Facts
2.1, 2.2 are literature inputs in HarmonicBalls/Proposed/LQG.lean, not Stmts), the derived inputs I1, I2 and the Green clause
of Prop 2.5 (E26). The edited Draft files are lc OK; `lb HarmonicBalls` with these statements built every tracked module
(the only failures were untracked or uncommitted work-in-progress files of other workers).

| Stmt | result | file:line | corrections applied |
|---|---|---|---|
| ExistenceUniquenessHarmonicBallsStmt | Theorem 1.1 | HarmonicBalls/Draft/Section1.lean:94 | [C6], [C7] |
| HarmonicBallNoveltyStmt | Theorem 1.2 | HarmonicBalls/Draft/Section1.lean:124 | [C6], [C7] (IsHarmonicBallFamily), [C12] (IsLipschitzDomain); freeze fix (2), 10a56e3 |
| HarmonicBallLocalSetStmt | Prop 1.3 | HarmonicBalls/Draft/Section1.lean:151 | [C6], [C7] (IsHarmonicBallFamily); reading t = 0 as {x} (E20(3), E21) |
| GreenFunctionBallStmt | Prop 2.3 | HarmonicBalls/Draft/Section2.lean:68 | none |
| LiouvilleVolumeGrowthStmt | Lemma 2.4 | HarmonicBalls/Draft/Section2.lean:89 | [C1]; PolyHighProb real exponent (d126f1b) |
| LQGMeasureFullSupportStmt | Input I1 | HarmonicBalls/Draft/Section2.lean:109 | none (derived input I1) |
| LQGVolumeGrowthAllScalesStmt | Input I2 | HarmonicBalls/Draft/Section2.lean:122 | [C1], [C2] (derived input I2) |
| GreenPotentialLiouvilleHolderStmt | Prop 2.5 | HarmonicBalls/Draft/Section2.lean:161 | freeze fix (5), 10a56e3; LBM clause [NCS1], not consumed |
| GreenPotentialHolderStmt | Prop 2.5 (Green clause) | HarmonicBalls/Draft/Section2.lean:190 | none (Green clause of 2.5, E26; the consumed form) |
| ReflectedLBMHeatKernelStmt | Prop 2.6 | HarmonicBalls/Draft/Section2.lean:225 | [C5]; [NCS1], not consumed |
| LeastSupersolutionMemStmt | Lemma 3.1 | HarmonicBalls/Draft/Section3.lean:47 | none |
| ClusterOpenLaplacianStmt | Lemma 3.2 | HarmonicBalls/Draft/Section3.lean:66 | [C3] |
| ClusterMonotoneStmt | Lemma 3.3 | HarmonicBalls/Draft/Section3.lean:89 | [C13] |
| ClusterConservationOfMassStmt | Lemma 3.4 | HarmonicBalls/Draft/Section3.lean:102 | [C3], [C4] |
| ClusterCompatibilityStmt | Lemma 3.5 | HarmonicBalls/Draft/Section3.lean:119 | [C3], [C14] |
| ObstacleLeastSuperharmonicMajorantStmt | Lemma A.1 | HarmonicBalls/Draft/SectionA.lean:48 | [C2] |
| ObstacleNonCoincidenceHarmonicStmt | Lemma A.2 | HarmonicBalls/Draft/SectionA.lean:62 | [C2] |
| ObstacleMonotoneStmt | Lemma A.3 | HarmonicBalls/Draft/SectionA.lean:73 | [C2] |
| ObstacleOdometerZeroBoundaryStmt | Lemma A.4 | HarmonicBalls/Draft/SectionA.lean:80 | [C2] |
| ObstacleConservationOfMassStmt | Lemma A.5 | HarmonicBalls/Draft/SectionA.lean:90 | [C2], [C4] |
| ObstacleCompatibilityStmt | Lemma A.6 | HarmonicBalls/Draft/SectionA.lean:105 | [C2], [C14] |
| ClusterLowerBoundStmt | Prop 4.1 | HarmonicBalls/Draft/Section4.lean:95 | [C3] |
| LeastSupersolutionHolderStmt | Lemma 4.2 | HarmonicBalls/Draft/Section4.lean:116 | [C8] |
| ClusterSubharmonicBallStmt | Lemma 4.3 | HarmonicBalls/Draft/Section4.lean:132 | [C3] |
| ClusterUpperBoundStmt | Prop 5.1 | HarmonicBalls/Draft/Section5.lean:122 | [C3] |
| ClusterContinuityStmt | Prop 5.2 | HarmonicBalls/Draft/Section5.lean:140 | [C18] |
| ClusterBoundaryMeasureZeroStmt | Prop 5.3 | HarmonicBalls/Draft/Section5.lean:155 | [C19] |
| RegularizedClusterHarmonicBallsStmt | Prop 5.4 | HarmonicBalls/Draft/Section5.lean:175 | [C9], [C20] |
| ExistenceHarmonicBallsStmt | Theorem 5.5 | HarmonicBalls/Draft/Section5.lean:192 | [C6] |
| UniquenessHarmonicBallsStmt | Prop 5.6 | HarmonicBalls/Draft/Section5.lean:206 | [C6], [C7] |
| ClusterScaleInvarianceStmt | Lemma 5.7 | HarmonicBalls/Draft/Section5.lean:226 | none |
| ClusterStrongCompatibilityStmt | Lemma 5.8 | HarmonicBalls/Draft/Section5.lean:246 | [C21] |
| HarnackTypeEstimateStmt | Prop 6.1 | HarmonicBalls/Draft/Section6.lean:204 | freeze fix (4) printed order E31, 1d4135b; PolyHighProb real exponent (d126f1b) |
| HarnackTypeComponentStmt | Prop 6.2 | HarmonicBalls/Draft/Section6.lean:228 | freeze fix (4) printed order E31, 1d4135b; PolyHighProb real exponent (d126f1b) |
| ManyGoodAnnuliStmt | Lemma 6.3 | HarmonicBalls/Draft/Section6.lean:253 | [C23] (IsGoodAnnulus); freeze fix (4) printed order E31, 1d4135b; PolyHighProb real exponent (d126f1b) |
| GoodAnnulusProbabilityStmt | Lemma 6.4 | HarmonicBalls/Draft/Section6.lean:268 | [C23], [C25] |
| AnnulusIterationStmt | Lemma 6.5 | HarmonicBalls/Draft/Section6.lean:287 | none (literature input, GM20b Lemma 3.1) |
| ManyVeryGoodAnnuliStmt | Lemma 6.6 | HarmonicBalls/Draft/Section6.lean:309 | [C23] (IsVeryGoodAnnulus); freeze fix (4) printed order E31, 1d4135b; PolyHighProb real exponent (d126f1b) |
| VeryGoodAnnulusProbabilityStmt | Lemma 6.7 | HarmonicBalls/Draft/Section6.lean:329 | [C23], [C26] |
| AnnulusMassBoundByOdometerStmt | Lemma 6.8 | HarmonicBalls/Draft/Section6.lean:350 | none |
| OdometerHarmonicMeasureBoundStmt | Lemma 6.9 | HarmonicBalls/Draft/Section6.lean:369 | [C24] |
| OdometerBoundByAnnulusMassStmt | Lemma 6.10 | HarmonicBalls/Draft/Section6.lean:386 | none |
| VeryGoodAnnulusHarnackTypeStmt | Lemma 6.11 | HarmonicBalls/Draft/Section6.lean:411 | [C23]; every C3 > 0 (G18, G28). OPEN: b after alpha_0, see note 2 |
| ShellDecompositionStmt | Lemma 6.12 | HarmonicBalls/Draft/Section6.lean:437 | none |
| LowMassSmallOdometerStmt | Lemma 6.13 | HarmonicBalls/Draft/Section6.lean:457 | [C15], [C23]; every C3 > 0 |
| ClusterUpperBoundPolyHighProbStmt | Prop 7.1 | HarmonicBalls/Draft/Section7.lean:51 | none; PolyHighProb real exponent (d126f1b) |
| ClusterTimeContinuityStmt | Prop 7.2 | HarmonicBalls/Draft/Section7.lean:70 | [C18], [C1] (range of beta^-) |
| BoundaryMeasureZeroOfCompactClusterStmt | Prop 8.1 | HarmonicBalls/Draft/Section8.lean:55 | none |
| TypicalPointManyGoodScalesStmt | Lemma 8.2 | HarmonicBalls/Draft/Section8.lean:74 | [C1] |
| OriginManyGoodScalesStmt | Lemma 8.3 | HarmonicBalls/Draft/Section8.lean:96 | [C1] |
| ObstacleComparisonStmt | Lemma 9.1 | HarmonicBalls/Draft/Section9.lean:83 | [C7], [C22] |
| SubharmonicBallUniquenessStmt | Prop 9.2 | HarmonicBalls/Draft/Section9.lean:106 | [C10]. OPEN: operator 04:35 ruled C10 UNCLEAR (Stmt = printed), see note 1 |
| HarmonicBallBoundarySubsetStmt | Lemma 9.3 | HarmonicBalls/Draft/Section9.lean:125 | [C7], [C22] |
| RegularOpenEqOfAEEqStmt | Lemma 9.4 | HarmonicBalls/Draft/Section9.lean:139 | none |
| ClusterBoundedCrossingsStmt | Lemma 10.1 | HarmonicBalls/Draft/Section10.lean:57 | none (alpha = alpha(gamma) before alpha_0, as printed; E22) |
| CrossingComponentContainsClusterCrossingStmt | Lemma 10.5 | HarmonicBalls/Draft/Section10.lean:81 | freeze fix (1), 10a56e3 |
| ComplementComponentBoundarySimpleLoopStmt | Prop 10.6 | HarmonicBalls/Draft/Section10.lean:103 | [C16] |
| HarmonicBallComplementBoundaryJordanStmt | Prop 10.7 | HarmonicBalls/Draft/Section10.lean:116 | [C6], [C7] (IsHarmonicBallFamily) |
| HarmonicBallNotLipschitzStmt | Prop 11.2 | HarmonicBalls/Draft/Section11.lean:136 | [C6], [C7] (IsHarmonicBallFamily), [C12] |
| NoConeConditionStmt | Lemma 11.5 | HarmonicBalls/Draft/Section11.lean:145 | none |
| AnnulusMassBoundByHarmonicChainStmt | Lemma 11.6 | HarmonicBalls/Draft/Section11.lean:160 | none |
| ManyConeBadScalesStmt | Lemma 11.7 | HarmonicBalls/Draft/Section11.lean:173 | none |
| ConeBadEventProbabilityStmt | Lemma 11.8 | HarmonicBalls/Draft/Section11.lean:186 | freeze fix (3) inner measure, 10a56e3 |
| SmallMetricDiameterLargeMassStmt | Prop 11.9 | HarmonicBalls/Draft/Section11.lean:201 | freeze fix (3) inner measure, 10a56e3 |
| SmallMetricDiameterLargeMassSquareStmt | Lemma 11.10 | HarmonicBalls/Draft/Section11.lean:217 | freeze fix (3) inner measure, 10a56e3 |
| HarmonicBallNotMetricBallStmt | Prop 11.11 | HarmonicBalls/Draft/Section11.lean:231 | [C6], [C7] (IsHarmonicBallFamily) |
| PinchEventPositiveProbabilityStmt | Lemma 11.12 | HarmonicBalls/Draft/Section11.lean:246 | [C11]; alpha_0 = 0 as printed ([C17] proof gap only); freeze fix (3) inner measure, 10a56e3 |
| ManyPinchScalesStmt | Lemma 11.13 | HarmonicBalls/Draft/Section11.lean:259 | none ([C17]: generalization of 11.12 as a carved step) |
| PinchEventMetricBallConsequenceStmt | Lemma 11.14 | HarmonicBalls/Draft/Section11.lean:275 | none |
| PinchFirstEventPositiveStmt | Lemma 11.15 | HarmonicBalls/Draft/Section11.lean:289 | freeze fix (3) inner measure, 10a56e3 |
| PinchSecondEventPositiveStmt | Lemma 11.16 | HarmonicBalls/Draft/Section11.lean:299 | freeze fix (3) inner measure, 10a56e3 |
| PinchThirdEventPositiveStmt | Lemma 11.17 | HarmonicBalls/Draft/Section11.lean:312 | freeze fix (3) inner measure, 10a56e3 |

Notes (open items for the operator; not changed, not in the fix list of 04:45):
1. Prop 9.2 `SubharmonicBallUniquenessStmt` still carries [C10] (conclusion `Λ ⊆ A`). The 04:35 verdict on C10 is UNCLEAR:
   "the Stmt is the PRINTED statement (int(closure Λ) ⊆ A); prove the weaker form as a separate theorem". Not applied (ESCALATIONS E33).
2. Lemma 6.11 `VeryGoodAnnulusHarnackTypeStmt` chooses `b` after `α₀` (b = b(γ, α₀, β⁻, C₃)); printed b = b(γ), and the 04:35 E22
   verdict lists 6.11 among the α₀-uniform statements to keep as printed. Fix (4) names only 6.1, 6.2, 6.3, 6.6 (ESCALATIONS E33).
3. PolyHighProb (Defs/Notation.lean:27) has a real exponent since d126f1b; its users (Lemma 2.4, Props 6.1, 6.2, Lemmas 6.3, 6.6,
   Prop 7.1, and the input WholePlaneLQGBallMassBounds of Proposed/LQG.lean) match line 336 and Ding-Gwynne Lemma 3.8.
