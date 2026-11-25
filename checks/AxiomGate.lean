-- Axiom gate for the numbered results.
-- Outside the default library (checks/ is not a lean_lib): compile with lc or `lake env lean checks/AxiomGate.lean`.
-- Imports: the modules of the counted declarations (docs/campaign/COUNTED-MANIFEST.md),
-- the DERIVED-row theorems of docs/campaign/PHASE2-DERIVATION-STATUS.md.

import HarmonicBalls.FirstPass.Canonical.NotMetricBall
import HarmonicBalls.FirstPass.Canonical.Novelty
import HarmonicBalls.FirstPass.Closure
import HarmonicBalls.FirstPass.Closure.Bridge12
import HarmonicBalls.FirstPass.Closure.RetiredInputs
import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.Closure.Sec6
import HarmonicBalls.FirstPass.Closure.Sec78910
import HarmonicBalls.FirstPass.Closure.SecA45
import HarmonicBalls.FirstPass.Phase2.CameronMartinMutualDerived
import HarmonicBalls.FirstPass.Phase2.CameronMartinReweightingDerived2
import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs11
import HarmonicBalls.FirstPass.Phase2.DerivedInputs17
import HarmonicBalls.FirstPass.Phase2.DerivedInputs19
import HarmonicBalls.FirstPass.Phase2.DerivedInputs23
import HarmonicBalls.FirstPass.Phase2.DerivedInputs3
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9
import HarmonicBalls.FirstPass.Phase2.InternalMetricClosedDerived
import HarmonicBalls.FirstPass.Phase2.LengthUnivDerived
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived
import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived
import HarmonicBalls.FirstPass.Phase2.PlaneDomainDerived
import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived
import HarmonicBalls.FirstPass.Phase2.WeylCompositionOuterDerived
import HarmonicBalls.FirstPass.Phase2.WeylInternalClosedDerived
import HarmonicBalls.FirstPass.Phase2.WeylScaledEuclideanDerived
import HarmonicBalls.FirstPass.Phase2.WeylShiftedMassDerived
import HarmonicBalls.FirstPass.Phase2.WeylShiftedSupDerived2
import HarmonicBalls.FirstPass.S11
import HarmonicBalls.FirstPass.S11b
import HarmonicBalls.FirstPass.S11d
import HarmonicBalls.FirstPass.S11e
import HarmonicBalls.FirstPass.S11i.Assembly13
import HarmonicBalls.FirstPass.S11i.Corrected11_13
import HarmonicBalls.FirstPass.S1S10
import HarmonicBalls.FirstPass.S1S10.CrossingLemma
import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.FirstPass.S5S7S8
import HarmonicBalls.FirstPass.S8c.BirkhoffDerived
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived
import HarmonicBalls.FirstPass.S9c
import HarmonicBalls.FirstPass.Phase2.DerivedInputs31
import HarmonicBalls.FirstPass.Phase2.DerivedInputs33
import HarmonicBalls.FirstPass.Phase2.DerivedInputs35
import HarmonicBalls.FirstPass.Phase2.DerivedInputs36
import HarmonicBalls.FirstPass.Phase2.DerivedInputs37
import HarmonicBalls.FirstPass.Phase2.DerivedInputs38
import HarmonicBalls.FirstPass.Phase2.DerivedInputs39
import HarmonicBalls.FirstPass.Phase2.DerivedInputs41
import HarmonicBalls.FirstPass.Phase2.ConnectedSquareUnionDiamDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs42
import HarmonicBalls.FirstPass.Phase2.DerivedInputs43
import HarmonicBalls.FirstPass.Phase2.DerivedInputs46
import HarmonicBalls.FirstPass.Phase2.DerivedInputs47
import HarmonicBalls.FirstPass.Phase2.PinchScalesLocalReplacementDerived
import HarmonicBalls.FirstPass.Phase2.NoveltyCanonicalLocalReplacementDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs44
import HarmonicBalls.FirstPass.Phase2.ConeBadScalesHolds
import HarmonicBalls.FirstPass.Phase2.WeylLogTruncationDerivedInputs
import HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer
import HarmonicBalls.Proofs.Sec6.FullThreeInputAssembly
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences
import HarmonicBalls.Proofs.Sec9.ObstacleComparison
import HarmonicBalls.Steps.Sec2.VolumeGrowth
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsAlphaZero
import HarmonicBalls.FirstPass.Phase2.LQGMetricXiPos
import HarmonicBalls.FirstPass.Phase2.Lemma1110LeafForms
import HarmonicBalls.FirstPass.Phase2.UnitTailCountedForms
import HarmonicBalls.FirstPass.Phase2.NotMetricBallCanonicalLeafForms
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsLeafForms
import HarmonicBalls.FirstPass.Phase2.DerivedInputsStep8Calibration
import HarmonicBalls.FirstPass.Phase2.Step8PerModelFrequency
import HarmonicBalls.FirstPass.Phase2.Step8PerModelUniv
import HarmonicBalls.FirstPass.Phase2.WeylExponentOfDG20
import HarmonicBalls.FirstPass.Phase2.LocalMetricReplacementDerivedCanonical
import HarmonicBalls.FirstPass.Phase2.CorrectedLemma11_12Derived
import HarmonicBalls.Proofs.Potential.LBMClauseSubcritical
import HarmonicBalls.Proofs.Potential.LQGClockInsertedEveryStart
import HarmonicBalls.Proofs.Sec11.MassDiamPositive
import HarmonicBalls.Proofs.Sec11.MassDiamFullField
import HarmonicBalls.FirstPass.Phase2.ForallXiCanonicalEquivalence
import HarmonicBalls.Proofs.Potential.GreenPotentialClassSupport
import HarmonicBalls.Proofs.Sec11.LipschitzDomainRotation
import HarmonicBalls.Proofs.Potential.GreenPotentialClassRelativeSupport
import HarmonicBalls.Proofs.Potential.LQGClockStrictEveryStart
import HarmonicBalls.Proofs.Potential.SquareClippedBallVolume
import HarmonicBalls.Proofs.Potential.ReflectedSquareScaling
import HarmonicBalls.Proofs.Potential.ReflectedBrownianFoldInvariance
import HarmonicBalls.Proofs.Potential.UniversalClock
import HarmonicBalls.Proofs.Potential.ReflectedClockIdentification
import HarmonicBalls.Proofs.Potential.ReflectedLebesgueInvariance
import HarmonicBalls.Proofs.Potential.ReflectedBrownianMarkov
import HarmonicBalls.Proofs.Potential.ReflectedGreenPotentialBound
import HarmonicBalls.Proofs.Potential.ReflectedRevuzFormula
import HarmonicBalls.Proofs.Potential.ReflectedRevuzIdentification
import HarmonicBalls.Proofs.Potential.ReflectedLQGRevuzMeasure

/-!
# Axiom gate

One `#print axioms` line per declaration, grouped by numbered result (N: counted declaration, X: forall-xi and
canonical-xi forms, P: Proofs-only results, D: derived-input theorem of a DERIVED row). Not part of the library.
-/


-- Counted declarations, one per numbered result (COUNTED-MANIFEST.md)
-- 1.1: firstPass_1_1 (HarmonicBalls/FirstPass/S1S10.lean:35)
#print axioms HarmonicBalls.firstPass_1_1
-- 1.2: firstPass_1_2 (HarmonicBalls/FirstPass/S1S10.lean:43)
#print axioms HarmonicBalls.firstPass_1_2
-- 1.3: firstPass_1_3 (HarmonicBalls/FirstPass/S1S10.lean:53)
#print axioms HarmonicBalls.firstPass_1_3
-- 2.3: closure_2_3 (HarmonicBalls/FirstPass/Closure.lean:113)
#print axioms HarmonicBalls.Closure.closure_2_3
-- 3.1: closure_3_1_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:125)
#print axioms HarmonicBalls.Closure.closure_3_1_derivedInputs39
-- 3.2: closure_3_2_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:135)
#print axioms HarmonicBalls.Closure.closure_3_2_derivedInputs39
-- 3.3: closure_3_3_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:149)
#print axioms HarmonicBalls.Closure.closure_3_3_derivedInputs39
-- 3.4: closure_3_4_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:159)
#print axioms HarmonicBalls.Closure.closure_3_4_derivedInputs39
-- 3.5: closure_3_5_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:172)
#print axioms HarmonicBalls.Closure.closure_3_5_derivedInputs39
-- 4.1: closure_4_1_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:182)
#print axioms HarmonicBalls.Closure.closure_4_1_derivedInputs39
-- 4.2: closure_4_2_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:192)
#print axioms HarmonicBalls.Closure.closure_4_2_derivedInputs39
-- 4.3: closure_4_3_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:202)
#print axioms HarmonicBalls.Closure.closure_4_3_derivedInputs39
-- 5.1: closure_5_1_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:212)
#print axioms HarmonicBalls.Closure.closure_5_1_derivedInputs39
-- 5.2: closure_5_2_derivedInputs19 (HarmonicBalls/FirstPass/Phase2/DerivedInputs19.lean:82)
#print axioms HarmonicBalls.Closure.closure_5_2_derivedInputs19
-- 5.3: firstPass_5_3 (HarmonicBalls/FirstPass/S5S7S8.lean:136)
#print axioms HarmonicBalls.firstPass_5_3
-- 5.4: firstPass_5_4 (HarmonicBalls/FirstPass/S5S7S8.lean:148)
#print axioms HarmonicBalls.firstPass_5_4
-- 5.5: firstPass_5_5 (HarmonicBalls/FirstPass/S5S7S8.lean:161)
#print axioms HarmonicBalls.firstPass_5_5
-- 5.6: closure_5_6_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:261)
#print axioms HarmonicBalls.Closure.closure_5_6_derivedInputs39
-- 5.7: closure_5_7_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:270)
#print axioms HarmonicBalls.Closure.closure_5_7_derivedInputs39
-- 5.8: closure_5_8_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:279)
#print axioms HarmonicBalls.Closure.closure_5_8_derivedInputs39
-- 6.1: closure_6_1_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:288)
#print axioms HarmonicBalls.Closure.closure_6_1_derivedInputs39
-- 6.2: closure_6_2_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:297)
#print axioms HarmonicBalls.Closure.closure_6_2_derivedInputs39
-- 6.3: closure_6_3_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:306)
#print axioms HarmonicBalls.Closure.closure_6_3_derivedInputs39
-- 6.4: closure_6_4_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:315)
#print axioms HarmonicBalls.Closure.closure_6_4_derivedInputs39
-- 6.6: closure_6_6_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:324)
#print axioms HarmonicBalls.Closure.closure_6_6_derivedInputs39
-- 6.7: closure_6_7_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:333)
#print axioms HarmonicBalls.Closure.closure_6_7_derivedInputs39
-- 6.8: closure_6_8_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:342)
#print axioms HarmonicBalls.Closure.closure_6_8_derivedInputs39
-- 6.9: closure_6_9_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:351)
#print axioms HarmonicBalls.Closure.closure_6_9_derivedInputs39
-- 6.10: closure_6_10_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:360)
#print axioms HarmonicBalls.Closure.closure_6_10_derivedInputs39
-- 6.11: closure_6_11_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:369)
#print axioms HarmonicBalls.Closure.closure_6_11_derivedInputs39
-- 6.12: closure_6_12_derivedInputs38 (HarmonicBalls/FirstPass/Phase2/DerivedInputs38.lean:141)
#print axioms HarmonicBalls.Closure.closure_6_12_derivedInputs38
-- 6.13: closure_6_13_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:378)
#print axioms HarmonicBalls.Closure.closure_6_13_derivedInputs39
-- 7.1: closure_7_1_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:387)
#print axioms HarmonicBalls.Closure.closure_7_1_derivedInputs39
-- 7.2: firstPass_7_2 (HarmonicBalls/FirstPass/S5S7S8.lean:52)
#print axioms HarmonicBalls.firstPass_7_2
-- 8.1: firstPass_8_1 (HarmonicBalls/FirstPass/S5S7S8.lean:72)
#print axioms HarmonicBalls.firstPass_8_1
-- 8.2: firstPass_8_2_S8d_noWeyl_derivedInputs23 (HarmonicBalls/FirstPass/Phase2/DerivedInputs23.lean:226)
#print axioms HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs23
-- 8.3: closure_8_3 (HarmonicBalls/FirstPass/Closure/Sec78910.lean:150)
#print axioms HarmonicBalls.Closure.closure_8_3
-- 9.3: firstPass_9_3_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:57)
#print axioms HarmonicBalls.firstPass_9_3_derivedInputs39
-- 9.4: firstPass_9_4_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:67)
#print axioms HarmonicBalls.firstPass_9_4_derivedInputs39
-- 10.1: firstPass_10_1 (HarmonicBalls/FirstPass/S1S10.lean:64)
#print axioms HarmonicBalls.firstPass_10_1
-- 10.6: firstPass_10_6 (HarmonicBalls/FirstPass/S1S10.lean:92)
#print axioms HarmonicBalls.firstPass_10_6
-- 10.7: firstPass_10_7 (HarmonicBalls/FirstPass/S1S10.lean:75)
#print axioms HarmonicBalls.firstPass_10_7
-- 11.2: firstPass_11_2 (HarmonicBalls/FirstPass/S11.lean:59)
#print axioms HarmonicBalls.firstPass_11_2
-- 11.5: firstPass_11_5 (HarmonicBalls/FirstPass/S11.lean:67)
#print axioms HarmonicBalls.firstPass_11_5
-- 11.6: closure_11_6_derivedInputs19 (HarmonicBalls/FirstPass/Phase2/DerivedInputs19.lean:240)
#print axioms HarmonicBalls.Closure.closure_11_6_derivedInputs19
-- 11.7: firstPass_11_7_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:77)
#print axioms HarmonicBalls.firstPass_11_7_derivedInputs39
-- 11.8: closure_11_8_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:448)
#print axioms HarmonicBalls.Closure.closure_11_8_derivedInputs39
-- 11.9: firstPass_11_9_derivedInputs38 (HarmonicBalls/FirstPass/Phase2/DerivedInputs38.lean:62)
#print axioms HarmonicBalls.firstPass_11_9_derivedInputs38
-- 11.10: firstPass_11_10_derivedInputs38 (HarmonicBalls/FirstPass/Phase2/DerivedInputs38.lean:151)
#print axioms HarmonicBalls.S11c.firstPass_11_10_derivedInputs38
-- 11.11: firstPass_11_11 (HarmonicBalls/FirstPass/S11.lean:111)
#print axioms HarmonicBalls.firstPass_11_11
-- 11.12: firstPass_11_12_derivedInputsAlphaZero (HarmonicBalls/FirstPass/Phase2/FieldAxiomsAlphaZero.lean:166)
#print axioms HarmonicBalls.firstPass_11_12_derivedInputsAlphaZero
-- 11.12 (metric inputs hDC hFin hAx only): firstPass_11_12_derivedInputsMetric (HarmonicBalls/FirstPass/Phase2/LQGMetricXiPos.lean:241)
#print axioms HarmonicBalls.firstPass_11_12_derivedInputsMetric
-- 11.12 (with the field-axiom binder): firstPass_11_12 (HarmonicBalls/FirstPass/S11e.lean:42)
#print axioms HarmonicBalls.firstPass_11_12
-- 11.13: manyPinchScales_of_corrected (HarmonicBalls/FirstPass/Closure/Bridge12.lean:322)
#print axioms HarmonicBalls.Closure.manyPinchScales_of_corrected
-- 11.14: closure_11_14 (HarmonicBalls/FirstPass/Closure/Sec11.lean:139)
#print axioms HarmonicBalls.Closure.closure_11_14
-- 11.15: firstPass_11_15_derivedInputs3 (HarmonicBalls/FirstPass/Phase2/DerivedInputs3.lean:945)
#print axioms HarmonicBalls.firstPass_11_15_derivedInputs3
-- 11.16: firstPass_11_16_of_11_17 (HarmonicBalls/FirstPass/S11e.lean:29)
#print axioms HarmonicBalls.firstPass_11_16_of_11_17
-- 11.16 (draft form, metric inputs hDC hFin hAx only): firstPass_11_16_derivedInputsMetric (HarmonicBalls/FirstPass/Phase2/LQGMetricXiPos.lean:249)
#print axioms HarmonicBalls.firstPass_11_16_derivedInputsMetric
-- 11.16: firstPass_11_16_corrected_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:97)
#print axioms HarmonicBalls.firstPass_11_16_corrected_derivedInputs39
-- 11.16 audit row: firstPass_11_16_corrected_derivedInputs (HarmonicBalls/FirstPass/Phase2/DerivedInputs31.lean:24)
#print axioms HarmonicBalls.firstPass_11_16_corrected_derivedInputs
-- 11.17 corrected form: firstPass_11_17_corrected_derivedInputs38 (HarmonicBalls/FirstPass/Phase2/DerivedInputs38.lean:75)
#print axioms HarmonicBalls.firstPass_11_17_corrected_derivedInputs38
-- 11.17 (draft form): pinchThirdEventPositiveStmt_derivedInputsMetric (HarmonicBalls/FirstPass/Phase2/LQGMetricXiPos.lean:233)
#print axioms HarmonicBalls.pinchThirdEventPositiveStmt_derivedInputsMetric
-- A.1: closure_A_1 (HarmonicBalls/FirstPass/Closure/SecA45.lean:37)
#print axioms HarmonicBalls.Closure.closure_A_1
-- A.2: closure_A_2 (HarmonicBalls/FirstPass/Closure/SecA45.lean:40)
#print axioms HarmonicBalls.Closure.closure_A_2
-- A.3: closure_A_3 (HarmonicBalls/FirstPass/Closure/SecA45.lean:43)
#print axioms HarmonicBalls.Closure.closure_A_3
-- A.4: closure_A_4 (HarmonicBalls/FirstPass/Closure/SecA45.lean:46)
#print axioms HarmonicBalls.Closure.closure_A_4
-- A.5: closure_A_5 (HarmonicBalls/FirstPass/Closure/SecA45.lean:49)
#print axioms HarmonicBalls.Closure.closure_A_5
-- A.6: closure_A_6 (HarmonicBalls/FirstPass/Closure/SecA45.lean:52)
#print axioms HarmonicBalls.Closure.closure_A_6

-- Numbered results whose only declaration is in Proofs/ (COUNTED-MANIFEST.md)
-- 2.4: liouvilleVolumeGrowthStmt_of_existence (HarmonicBalls/Proofs/Sec9/LQGExistenceConsequences.lean:30)
#print axioms HarmonicBalls.liouvilleVolumeGrowthStmt_of_existence
-- 2.4: liouvilleVolumeGrowthStmt_of_ballMass (HarmonicBalls/Steps/Sec2/VolumeGrowth.lean:80)
#print axioms HarmonicBalls.liouvilleVolumeGrowthStmt_of_ballMass
-- 6.5: annulusIterationStmt_of_three_inputs (HarmonicBalls/Proofs/Sec6/FullThreeInputAssembly.lean:73)
#print axioms HarmonicBalls.Section6Full.annulusIterationStmt_of_three_inputs
-- 6.5: annulusIterationStmt_proved (HarmonicBalls/Proofs/Sec6/AnnulusLawTransfer.lean:207)
#print axioms HarmonicBalls.Section6.annulusIterationStmt_proved
-- 9.1: obstacleComparison (HarmonicBalls/Proofs/Sec9/ObstacleComparison.lean:32)
#print axioms HarmonicBalls.obstacleComparison
-- 9.2 corrected form [C51]: firstPass_9_2_corrected (HarmonicBalls/FirstPass/S9c.lean:116)
#print axioms HarmonicBalls.S9c.firstPass_9_2_corrected
-- 9.2: closure_9_2_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:457)
#print axioms HarmonicBalls.Closure.closure_9_2_derivedInputs39
-- 10.5 corrected form [C48]: firstPass_10_5_corrected (HarmonicBalls/FirstPass/S1S10/CrossingLemma.lean:38)
#print axioms HarmonicBalls.firstPass_10_5_corrected
-- 5.2: closure_5_2_derivedInputs33 (HarmonicBalls/FirstPass/Phase2/DerivedInputs33.lean:25)
#print axioms HarmonicBalls.Closure.closure_5_2_derivedInputs33
-- 8.2: firstPass_8_2_S8d_noWeyl_derivedInputs33 (HarmonicBalls/FirstPass/Phase2/DerivedInputs33.lean:74)
#print axioms HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs33
-- 8.3: closure_8_3_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:416)
#print axioms HarmonicBalls.Closure.closure_8_3_derivedInputs39
-- 11.6: closure_11_6_derivedInputs33 (HarmonicBalls/FirstPass/Phase2/DerivedInputs33.lean:40)
#print axioms HarmonicBalls.Closure.closure_11_6_derivedInputs33

-- Forall-xi and canonical-xi forms (COUNTED-MANIFEST.md)
-- 11.13 forall-xi `CorrectedLemma11_13Stmt`: correctedLemma11_13_of_identity (HarmonicBalls/FirstPass/S11i/Assembly13.lean:79)
#print axioms HarmonicBalls.correctedLemma11_13_of_identity
-- 1.2 canonical-xi `HarmonicBallNoveltyCanonicalStmt`: harmonicBallNoveltyStmt_of_existence_and_results_canonical (HarmonicBalls/FirstPass/Canonical/Novelty.lean:23)
#print axioms HarmonicBalls.harmonicBallNoveltyStmt_of_existence_and_results_canonical
-- 11.11 canonical-xi `HarmonicBallNotMetricBallCanonicalStmt`: harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth (HarmonicBalls/FirstPass/Canonical/NotMetricBall.lean:129)
#print axioms HarmonicBalls.harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth
-- 11.13 canonical-xi `CorrectedLemma11_13CanonicalStmt`: firstPass_11_13_canonical (HarmonicBalls/FirstPass/S11i/Corrected11_13.lean:127)
#print axioms HarmonicBalls.firstPass_11_13_canonical

-- Derived-input theorems of DERIVED rows (PHASE2-DERIVATION-STATUS.md)
-- row 5: lqgMeasureWeylScaling (HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean:124)
#print axioms HarmonicBalls.Section6.lqgMeasureWeylScaling
-- row 6: lqgMeasureOfProfileMeasurable_derived (HarmonicBalls/FirstPass/Phase2/ProfileDecoderDerived.lean:401)
#print axioms HarmonicBalls.lqgMeasureOfProfileMeasurable_derived
-- row 7: birkhoffPointwiseErgodic_derived (HarmonicBalls/FirstPass/S8c/BirkhoffDerived.lean:21)
#print axioms HarmonicBalls.birkhoffPointwiseErgodic_derived
-- row 10: WholePlaneGFFAffineInvariance_derived (HarmonicBalls/FirstPass/Phase2/DerivedInputs11.lean:26)
#print axioms HarmonicBalls.WholePlaneGFFAffineInvariance_derived
-- row 11: localLQGInsertionWeylOffOrigin_derived (HarmonicBalls/FirstPass/S8c/WeylOffOriginDerived.lean:88)
#print axioms HarmonicBalls.localLQGInsertionWeylOffOrigin_derived
-- row 13: cameronMartinGFFMutualAbsCont_derived (HarmonicBalls/FirstPass/Phase2/DerivedInputs9.lean:37)
#print axioms HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived
-- row 13: cameronMartinGFFMutualAbsCont_derived (HarmonicBalls/FirstPass/Phase2/CameronMartinMutualDerived.lean:56)
#print axioms HarmonicBalls.cameronMartinGFFMutualAbsCont_derived
-- row 15: localLQGDecoderCommonFrozen_derived (HarmonicBalls/FirstPass/Phase2/LocalDecoderCommonDerived.lean:1859)
#print axioms HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived
-- row 21: lqgMassFunctionalMeasurable_derived (HarmonicBalls/FirstPass/Phase2/MassFunctionalDerived.lean:702)
#print axioms HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived
-- row 22: lqgMeasureSquareMeasurable_derived' (HarmonicBalls/FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean:192)
#print axioms HarmonicBalls.lqgMeasureSquareMeasurable_derived'
-- row 26: weylInternalClosed_derived (HarmonicBalls/FirstPass/Phase2/WeylInternalClosedDerived.lean:149)
#print axioms HarmonicBalls.weylInternalClosed_derived
-- row 27: weylShiftedMassMeasurable_derived (HarmonicBalls/FirstPass/Phase2/WeylShiftedMassDerived.lean:96)
#print axioms HarmonicBalls.weylShiftedMassMeasurable_derived
-- row 28: weylShiftedSupMeasurable_derived (HarmonicBalls/FirstPass/Phase2/WeylShiftedSupDerived2.lean:124)
#print axioms HarmonicBalls.weylShiftedSupMeasurable_derived
-- row 33: lqgMassInnerMeasurable_derived' (HarmonicBalls/FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean:198)
#print axioms HarmonicBalls.lqgMassInnerMeasurable_derived'
-- row 35: planeDomainMinusConvexCompactPreconnected_derived (HarmonicBalls/FirstPass/Phase2/PlaneDomainDerived.lean:14)
#print axioms HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived
-- row 37: cameronMartinGFFReweighting_derived (HarmonicBalls/FirstPass/Phase2/CameronMartinReweightingDerived2.lean:267)
#print axioms HarmonicBalls.S11aj.cameronMartinGFFReweighting_derived
-- row 39: internalMetricClosedEqIInfThickening_derived (HarmonicBalls/FirstPass/Phase2/InternalMetricClosedDerived.lean:409)
#print axioms HarmonicBalls.internalMetricClosedEqIInfThickening_derived
-- row 42: lqgMetricLengthUniv_derived (HarmonicBalls/FirstPass/Phase2/LengthUnivDerived.lean:30)
#print axioms HarmonicBalls.lqgMetricLengthUniv_derived
-- row 49: lqgMeasureLocality_derived (HarmonicBalls/FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean:185)
#print axioms HarmonicBalls.lqgMeasureLocality_derived
-- row 51: localMeasureKernelStmt_derived (HarmonicBalls/FirstPass/Phase2/LocalDecoderCommonDerived.lean:1564)
#print axioms HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived
-- row 56: weylMetricCompositionContinuousOuter_derived (HarmonicBalls/FirstPass/Phase2/WeylCompositionOuterDerived.lean:1221)
#print axioms HarmonicBalls.weylMetricCompositionContinuousOuter_derived
-- row 57: weylScaledEuclidean_derived (HarmonicBalls/FirstPass/Phase2/WeylScaledEuclideanDerived.lean:93)
#print axioms HarmonicBalls.weylScaledEuclidean_derived
-- Round 36: counted forms with the phase-torus ergodicity input supplied (COUNTED-MANIFEST.md, round-36 refresh)
-- 1.3: closure_1_3_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:115)
#print axioms HarmonicBalls.Closure.closure_1_3_derivedInputs39
-- 5.2: closure_5_2_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:221)
#print axioms HarmonicBalls.Closure.closure_5_2_derivedInputs39
-- 5.3: closure_5_3_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:231)
#print axioms HarmonicBalls.Closure.closure_5_3_derivedInputs39
-- 5.4: closure_5_4_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:241)
#print axioms HarmonicBalls.Closure.closure_5_4_derivedInputs39
-- 5.5: closure_5_5_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:251)
#print axioms HarmonicBalls.Closure.closure_5_5_derivedInputs39
-- 7.2: closure_7_2_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:396)
#print axioms HarmonicBalls.Closure.closure_7_2_derivedInputs39
-- 8.1: closure_8_1_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:406)
#print axioms HarmonicBalls.Closure.closure_8_1_derivedInputs39
-- 8.2: firstPass_8_2_S8d_noWeyl_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:46)
#print axioms HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs39
-- 9.2: closure_9_2_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:457)
#print axioms HarmonicBalls.Closure.closure_9_2_derivedInputs39
-- 10.7: closure_10_7_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:427)
#print axioms HarmonicBalls.Closure.closure_10_7_derivedInputs39
-- 11.6: closure_11_6_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:438)
#print axioms HarmonicBalls.Closure.closure_11_6_derivedInputs39

-- Closure forms with the whole-plane GFF existence and closed internal-metric inputs supplied (not counted rows)
-- closure_11_12_clean_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:34)
#print axioms HarmonicBalls.Closure.closure_11_12_clean_derived
-- closure_1_2_canonical_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:74)
#print axioms HarmonicBalls.Closure.closure_1_2_canonical_derived
-- closure_1_2_faithful_canonical_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:136)
#print axioms HarmonicBalls.Closure.closure_1_2_faithful_canonical_derived
-- closure_11_13_paperExponent_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:198)
#print axioms HarmonicBalls.Closure.closure_11_13_paperExponent_derived
-- closure_11_11_paperExponent_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:241)
#print axioms HarmonicBalls.Closure.closure_11_11_paperExponent_derived
-- closure_1_2_paperExponent_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:292)
#print axioms HarmonicBalls.Closure.closure_1_2_paperExponent_derived
-- closure_11_15_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:356)
#print axioms HarmonicBalls.Closure.closure_11_15_derived
-- closure_11_16_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:366)
#print axioms HarmonicBalls.Closure.closure_11_16_derived
-- closure_11_17_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:397)
#print axioms HarmonicBalls.Closure.closure_11_17_derived
-- closure_11_12_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:429)
#print axioms HarmonicBalls.Closure.closure_11_12_derived
-- closure_11_13_canonical_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:469)
#print axioms HarmonicBalls.Closure.closure_11_13_canonical_derived
-- closure_11_11_canonical_derived (HarmonicBalls/FirstPass/Closure/RetiredInputs.lean:511)
#print axioms HarmonicBalls.Closure.closure_11_11_canonical_derived

-- Round 41: counted forms with the further hypotheses removed (supersede the round-39 forms of the same rows; COUNTED-MANIFEST.md, round-41 refresh)
-- 8.2: firstPass_8_2_S8d_noWeyl_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:24)
#print axioms HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs41
-- 9.3: firstPass_9_3_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:33)
#print axioms HarmonicBalls.firstPass_9_3_derivedInputs41
-- 9.4: firstPass_9_4_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:40)
#print axioms HarmonicBalls.firstPass_9_4_derivedInputs41
-- 11.9: firstPass_11_9_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:47)
#print axioms HarmonicBalls.firstPass_11_9_derivedInputs41
-- 9.2 corrected: firstPass_9_2_corrected_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:56)
#print axioms HarmonicBalls.firstPass_9_2_corrected_derivedInputs41
-- 1.3: closure_1_3_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:68)
#print axioms HarmonicBalls.Closure.closure_1_3_derivedInputs41
-- 3.1: closure_3_1_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:77)
#print axioms HarmonicBalls.Closure.closure_3_1_derivedInputs41
-- 3.2: closure_3_2_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:84)
#print axioms HarmonicBalls.Closure.closure_3_2_derivedInputs41
-- 3.3: closure_3_3_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:91)
#print axioms HarmonicBalls.Closure.closure_3_3_derivedInputs41
-- 3.4: closure_3_4_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:98)
#print axioms HarmonicBalls.Closure.closure_3_4_derivedInputs41
-- 3.5: closure_3_5_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:105)
#print axioms HarmonicBalls.Closure.closure_3_5_derivedInputs41
-- 4.1: closure_4_1_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:112)
#print axioms HarmonicBalls.Closure.closure_4_1_derivedInputs41
-- 4.2: closure_4_2_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:119)
#print axioms HarmonicBalls.Closure.closure_4_2_derivedInputs41
-- 4.3: closure_4_3_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:126)
#print axioms HarmonicBalls.Closure.closure_4_3_derivedInputs41
-- 5.1: closure_5_1_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:133)
#print axioms HarmonicBalls.Closure.closure_5_1_derivedInputs41
-- 5.2: closure_5_2_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:140)
#print axioms HarmonicBalls.Closure.closure_5_2_derivedInputs41
-- 5.3: closure_5_3_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:149)
#print axioms HarmonicBalls.Closure.closure_5_3_derivedInputs41
-- 5.4: closure_5_4_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:158)
#print axioms HarmonicBalls.Closure.closure_5_4_derivedInputs41
-- 5.5: closure_5_5_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:167)
#print axioms HarmonicBalls.Closure.closure_5_5_derivedInputs41
-- 5.6: closure_5_6_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:176)
#print axioms HarmonicBalls.Closure.closure_5_6_derivedInputs41
-- 5.7: closure_5_7_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:183)
#print axioms HarmonicBalls.Closure.closure_5_7_derivedInputs41
-- 5.8: closure_5_8_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:191)
#print axioms HarmonicBalls.Closure.closure_5_8_derivedInputs41
-- 6.1: closure_6_1_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:198)
#print axioms HarmonicBalls.Closure.closure_6_1_derivedInputs41
-- 6.2: closure_6_2_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:205)
#print axioms HarmonicBalls.Closure.closure_6_2_derivedInputs41
-- 6.3: closure_6_3_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:212)
#print axioms HarmonicBalls.Closure.closure_6_3_derivedInputs41
-- 6.4: closure_6_4_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:219)
#print axioms HarmonicBalls.Closure.closure_6_4_derivedInputs41
-- 6.6: closure_6_6_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:226)
#print axioms HarmonicBalls.Closure.closure_6_6_derivedInputs41
-- 6.7: closure_6_7_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:233)
#print axioms HarmonicBalls.Closure.closure_6_7_derivedInputs41
-- 6.8: closure_6_8_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:240)
#print axioms HarmonicBalls.Closure.closure_6_8_derivedInputs41
-- 6.9: closure_6_9_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:247)
#print axioms HarmonicBalls.Closure.closure_6_9_derivedInputs41
-- 6.10: closure_6_10_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:254)
#print axioms HarmonicBalls.Closure.closure_6_10_derivedInputs41
-- 6.11: closure_6_11_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:261)
#print axioms HarmonicBalls.Closure.closure_6_11_derivedInputs41
-- 6.13: closure_6_13_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:268)
#print axioms HarmonicBalls.Closure.closure_6_13_derivedInputs41
-- 7.1: closure_7_1_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:275)
#print axioms HarmonicBalls.Closure.closure_7_1_derivedInputs41
-- 7.2: closure_7_2_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:282)
#print axioms HarmonicBalls.Closure.closure_7_2_derivedInputs41
-- 8.1: closure_8_1_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:291)
#print axioms HarmonicBalls.Closure.closure_8_1_derivedInputs41
-- 8.3: closure_8_3_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:300)
#print axioms HarmonicBalls.Closure.closure_8_3_derivedInputs41
-- 10.7: closure_10_7_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:310)
#print axioms HarmonicBalls.Closure.closure_10_7_derivedInputs41
-- 11.6: closure_11_6_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:320)
#print axioms HarmonicBalls.Closure.closure_11_6_derivedInputs41
-- 11.8: closure_11_8_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:329)
#print axioms HarmonicBalls.Closure.closure_11_8_derivedInputs41
-- 9.2: closure_9_2_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:336)
#print axioms HarmonicBalls.Closure.closure_9_2_derivedInputs41
-- 11.10: firstPass_11_10_derivedInputs41 (HarmonicBalls/FirstPass/Phase2/DerivedInputs41.lean:349)
#print axioms HarmonicBalls.S11c.firstPass_11_10_derivedInputs41

-- Round 42: counted forms with the further hypotheses removed (supersede the round-41 forms of the same rows)
-- 8.3: closure_8_3_derivedInputs42 (HarmonicBalls/FirstPass/Phase2/DerivedInputs42.lean:24)
#print axioms HarmonicBalls.Closure.closure_8_3_derivedInputs42
-- 11.10: firstPass_11_10_derivedInputs42 (HarmonicBalls/FirstPass/Phase2/DerivedInputs42.lean:37)
#print axioms HarmonicBalls.S11c.firstPass_11_10_derivedInputs42
-- 11.10: firstPass_11_10_derivedInputsWeylShiftedSup (HarmonicBalls/FirstPass/Phase2/WeylShiftedChainDerived.lean:108)
#print axioms HarmonicBalls.S11c.firstPass_11_10_derivedInputsWeylShiftedSup

-- Round 43: counted forms with the closed-square case in place of hFin (11.10) and without hMet (11.9)
-- 11.10: firstPass_11_10_derivedInputsClosedSquare (HarmonicBalls/FirstPass/Phase2/ConnectedSquareUnionDiamDerived.lean:94)
#print axioms HarmonicBalls.S11c.firstPass_11_10_derivedInputsClosedSquare
-- 11.9: firstPass_11_9_derivedInputsFieldAxioms (HarmonicBalls/FirstPass/Phase2/WeylLogTruncationDerivedInputs.lean:50)
#print axioms HarmonicBalls.firstPass_11_9_derivedInputsFieldAxioms

-- Round 43: counted forms with the unused hypotheses removed (supersede the earlier forms of the same rows)
-- firstPass_1_1_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:47)
#print axioms HarmonicBalls.firstPass_1_1_derivedInputs43
-- firstPass_1_2_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:56)
#print axioms HarmonicBalls.firstPass_1_2_derivedInputs43
-- firstPass_8_2_S8d_noWeyl_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:73)
#print axioms HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs43
-- firstPass_9_3_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:79)
#print axioms HarmonicBalls.firstPass_9_3_derivedInputs43
-- firstPass_9_4_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:85)
#print axioms HarmonicBalls.firstPass_9_4_derivedInputs43
-- firstPass_10_1_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:91)
#print axioms HarmonicBalls.firstPass_10_1_derivedInputs43
-- firstPass_10_6_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:100)
#print axioms HarmonicBalls.firstPass_10_6_derivedInputs43
-- firstPass_11_2_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:111)
#print axioms HarmonicBalls.firstPass_11_2_derivedInputs43
-- firstPass_11_5_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:122)
#print axioms HarmonicBalls.firstPass_11_5_derivedInputs43
-- firstPass_11_7_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:134)
#print axioms HarmonicBalls.firstPass_11_7_derivedInputs43
-- firstPass_11_11_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:144)
#print axioms HarmonicBalls.firstPass_11_11_derivedInputs43
-- liouvilleVolumeGrowthStmt_of_ballMass_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:156)
#print axioms HarmonicBalls.liouvilleVolumeGrowthStmt_of_ballMass_derivedInputs43
-- firstPass_9_2_corrected_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:164)
#print axioms HarmonicBalls.firstPass_9_2_corrected_derivedInputs43
-- firstPass_11_16_corrected_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:172)
#print axioms HarmonicBalls.firstPass_11_16_corrected_derivedInputs43
-- firstPass_11_17_corrected_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:187)
#print axioms HarmonicBalls.firstPass_11_17_corrected_derivedInputs43
-- harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:196)
#print axioms HarmonicBalls.harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs43
-- harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:214)
#print axioms HarmonicBalls.harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth_derivedInputs43
-- closure_1_3_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:230)
#print axioms HarmonicBalls.Closure.closure_1_3_derivedInputs43
-- closure_3_1_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:236)
#print axioms HarmonicBalls.Closure.closure_3_1_derivedInputs43
-- closure_3_2_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:242)
#print axioms HarmonicBalls.Closure.closure_3_2_derivedInputs43
-- closure_3_3_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:248)
#print axioms HarmonicBalls.Closure.closure_3_3_derivedInputs43
-- closure_3_4_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:254)
#print axioms HarmonicBalls.Closure.closure_3_4_derivedInputs43
-- closure_3_5_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:260)
#print axioms HarmonicBalls.Closure.closure_3_5_derivedInputs43
-- closure_4_1_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:266)
#print axioms HarmonicBalls.Closure.closure_4_1_derivedInputs43
-- closure_4_2_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:272)
#print axioms HarmonicBalls.Closure.closure_4_2_derivedInputs43
-- closure_4_3_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:278)
#print axioms HarmonicBalls.Closure.closure_4_3_derivedInputs43
-- closure_5_1_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:284)
#print axioms HarmonicBalls.Closure.closure_5_1_derivedInputs43
-- closure_5_2_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:290)
#print axioms HarmonicBalls.Closure.closure_5_2_derivedInputs43
-- closure_5_3_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:296)
#print axioms HarmonicBalls.Closure.closure_5_3_derivedInputs43
-- closure_5_4_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:302)
#print axioms HarmonicBalls.Closure.closure_5_4_derivedInputs43
-- closure_5_5_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:308)
#print axioms HarmonicBalls.Closure.closure_5_5_derivedInputs43
-- closure_5_6_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:314)
#print axioms HarmonicBalls.Closure.closure_5_6_derivedInputs43
-- closure_5_7_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:320)
#print axioms HarmonicBalls.Closure.closure_5_7_derivedInputs43
-- closure_5_8_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:326)
#print axioms HarmonicBalls.Closure.closure_5_8_derivedInputs43
-- closure_6_1_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:332)
#print axioms HarmonicBalls.Closure.closure_6_1_derivedInputs43
-- closure_6_2_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:338)
#print axioms HarmonicBalls.Closure.closure_6_2_derivedInputs43
-- closure_6_3_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:344)
#print axioms HarmonicBalls.Closure.closure_6_3_derivedInputs43
-- closure_6_4_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:350)
#print axioms HarmonicBalls.Closure.closure_6_4_derivedInputs43
-- closure_6_6_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:356)
#print axioms HarmonicBalls.Closure.closure_6_6_derivedInputs43
-- closure_6_7_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:362)
#print axioms HarmonicBalls.Closure.closure_6_7_derivedInputs43
-- closure_6_8_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:368)
#print axioms HarmonicBalls.Closure.closure_6_8_derivedInputs43
-- closure_6_9_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:374)
#print axioms HarmonicBalls.Closure.closure_6_9_derivedInputs43
-- closure_6_10_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:380)
#print axioms HarmonicBalls.Closure.closure_6_10_derivedInputs43
-- closure_6_11_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:386)
#print axioms HarmonicBalls.Closure.closure_6_11_derivedInputs43
-- closure_6_13_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:392)
#print axioms HarmonicBalls.Closure.closure_6_13_derivedInputs43
-- closure_7_1_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:398)
#print axioms HarmonicBalls.Closure.closure_7_1_derivedInputs43
-- closure_7_2_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:404)
#print axioms HarmonicBalls.Closure.closure_7_2_derivedInputs43
-- closure_8_1_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:410)
#print axioms HarmonicBalls.Closure.closure_8_1_derivedInputs43
-- closure_8_3_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:417)
#print axioms HarmonicBalls.Closure.closure_8_3_derivedInputs43
-- closure_10_7_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:425)
#print axioms HarmonicBalls.Closure.closure_10_7_derivedInputs43
-- closure_11_6_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:432)
#print axioms HarmonicBalls.Closure.closure_11_6_derivedInputs43
-- closure_11_8_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:438)
#print axioms HarmonicBalls.Closure.closure_11_8_derivedInputs43
-- closure_9_2_derivedInputs43 (HarmonicBalls/FirstPass/Phase2/DerivedInputs43.lean:445)
#print axioms HarmonicBalls.Closure.closure_9_2_derivedInputs43

-- Round 46: counted forms with the input TorhorstSimpleLoopFrozen supplied (supersede the earlier forms of the same rows)
-- 10.6: firstPass_10_6_derivedInputs46 (HarmonicBalls/FirstPass/Phase2/DerivedInputs46.lean:27)
#print axioms HarmonicBalls.firstPass_10_6_derivedInputs46
-- 10.7: closure_10_7_derivedInputs46 (HarmonicBalls/FirstPass/Phase2/DerivedInputs46.lean:118)
#print axioms HarmonicBalls.Closure.closure_10_7_derivedInputs46
-- 10.5 corrected form [C48]: firstPass_10_5_corrected_derivedInputs46 (HarmonicBalls/FirstPass/Phase2/DerivedInputs46.lean:82)
#print axioms HarmonicBalls.firstPass_10_5_corrected_derivedInputs46
-- 1.2: firstPass_1_2_derivedInputs47 (HarmonicBalls/FirstPass/Phase2/DerivedInputs47.lean:20)
#print axioms HarmonicBalls.firstPass_1_2_derivedInputs47
-- 1.2 canonical-xi: harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs47 (HarmonicBalls/FirstPass/Phase2/DerivedInputs47.lean:30)
#print axioms HarmonicBalls.harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs47
-- 8.3: closure_8_3_derivedInputs44 (HarmonicBalls/FirstPass/Phase2/DerivedInputs44.lean:70)
#print axioms HarmonicBalls.Closure.closure_8_3_derivedInputs44
-- 11.7: manyConeBadScalesStmt_holds (HarmonicBalls/FirstPass/Phase2/ConeBadScalesHolds.lean:31)
#print axioms HarmonicBalls.manyConeBadScalesStmt_holds
-- 11.10: firstPass_11_10_derivedInputsClosedSquarePositive (HarmonicBalls/FirstPass/Phase2/Lemma1110LeafForms.lean:28)
#print axioms HarmonicBalls.S11c.firstPass_11_10_derivedInputsClosedSquarePositive
-- 11.13 canonical-xi at universe 0: firstPass_11_13_canonical_of_seedInputs_metricInputs (HarmonicBalls/FirstPass/Phase2/Lemma1110LeafForms.lean:47)
#print axioms HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed.firstPass_11_13_canonical_of_seedInputs_metricInputs
-- 11.13 canonical-xi at universe 0: firstPass_11_13_canonical_of_seedInputs_lemma11_10 (HarmonicBalls/FirstPass/Phase2/Step8WholePlaneFromSeed.lean:128)
#print axioms HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed.firstPass_11_13_canonical_of_seedInputs_lemma11_10
-- 11.11 canonical-xi: harmonicBallNotMetricBallCanonicalStmt_of_pinch_fieldAxioms (HarmonicBalls/FirstPass/Phase2/NotMetricBallCanonicalLeafForms.lean:24)
#print axioms HarmonicBalls.harmonicBallNotMetricBallCanonicalStmt_of_pinch_fieldAxioms
-- 11.11: firstPass_11_11_fieldAxioms (HarmonicBalls/FirstPass/Phase2/FieldAxiomsLeafForms.lean:28)
#print axioms HarmonicBalls.firstPass_11_11_fieldAxioms
-- 11.15: firstPass_11_15_fieldAxioms (HarmonicBalls/FirstPass/Phase2/FieldAxiomsLeafForms.lean:35)
#print axioms HarmonicBalls.firstPass_11_15_fieldAxioms
-- 2.4 (cited, no hypothesis): liouvilleVolumeGrowthStmt_of_ballMass_derivedInputs44 (HarmonicBalls/FirstPass/Phase2/DerivedInputs44.lean:23)
#print axioms HarmonicBalls.liouvilleVolumeGrowthStmt_of_ballMass_derivedInputs44
-- 11.13 canonical-xi: firstPass_11_13_canonical_derivedInputsCalibration (HarmonicBalls/FirstPass/Phase2/DerivedInputsStep8Calibration.lean:30)
#print axioms HarmonicBalls.firstPass_11_13_canonical_derivedInputsCalibration
-- 11.13 canonical-xi: firstPass_11_13_canonical_of_perModelFrequency (HarmonicBalls/FirstPass/Phase2/Step8PerModelFrequency.lean:56)
#print axioms HarmonicBalls.firstPass_11_13_canonical_of_perModelFrequency
-- 11.13 canonical-xi, Step 8 at every universe (HarmonicBalls/FirstPass/Phase2/Step8PerModelUniv.lean)
#print axioms HarmonicBalls.step8CertificateFrequencyPerModel_univ_of_zero
#print axioms HarmonicBalls.firstPass_11_13_canonical_univ_of_seedInputs_metricInputs
-- field axioms at every universe from Type (HarmonicBalls/FirstPass/Phase2/FieldAxiomsUniv.lean)
#print axioms HarmonicBalls.lqgMetricFieldAxiomsUnivFrozen_of_zero
#print axioms HarmonicBalls.firstPass_11_13_canonical_univ_of_metricInputsZero
-- 11.10 and 11.17 (field axioms and unit-square crossing tail; HarmonicBalls/FirstPass/Phase2/UnitTailCountedForms.lean)
#print axioms HarmonicBalls.dyadicCellDiamSmallFrozen_of_unitTail_xiPos
#print axioms HarmonicBalls.connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos
#print axioms HarmonicBalls.S11c.firstPass_11_10_derivedInputsUnitTail
#print axioms HarmonicBalls.pinchThirdEventPositiveStmt_derivedInputsUnitTail
#print axioms HarmonicBalls.firstPass_11_16_derivedInputsUnitTail
#print axioms HarmonicBalls.firstPass_11_12_derivedInputsUnitTail
#print axioms HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed.firstPass_11_13_canonical_of_seedInputs_unitTail
-- canonical-xi from the local metric replacement alone (binder hN2): 11.13, 11.11 (HarmonicBalls/FirstPass/Phase2/PinchScalesLocalReplacementDerived.lean), 1.2 (HarmonicBalls/FirstPass/Phase2/NoveltyCanonicalLocalReplacementDerived.lean:21)
#print axioms HarmonicBalls.correctedLemma11_13Canonical_of_localMetricReplacement_derived
#print axioms HarmonicBalls.harmonicBallNotMetricBallCanonical_of_localMetricReplacement_derived
#print axioms HarmonicBalls.harmonicBallNoveltyCanonical_of_localMetricReplacement_derived
-- every-xi forms with no hypothesis: 11.13, 11.11, 1.2 and the Weyl exponent xi = gamma / d_gamma (HarmonicBalls/FirstPass/Phase2/WeylExponentOfDG20.lean:66, :72, :76, :80)
#print axioms HarmonicBalls.xi_eq_xiGamma_derived
#print axioms HarmonicBalls.correctedLemma11_13_forallXi_derived
#print axioms HarmonicBalls.firstPass_11_11_forallXi_derived
#print axioms HarmonicBalls.firstPass_1_2_forallXi_derived
-- canonical-exponent forms with no hypothesis: 11.13, 11.11, 1.2 (HarmonicBalls/FirstPass/Phase2/LocalMetricReplacementDerivedCanonical.lean:24, :28, :32)
#print axioms HarmonicBalls.correctedLemma11_13Canonical_derived
#print axioms HarmonicBalls.harmonicBallNotMetricBallCanonical_derived
#print axioms HarmonicBalls.harmonicBallNoveltyCanonical_derived
-- 2.5: the frozen statement at every universe (HarmonicBalls/Proofs/Potential/LBMClauseSubcritical.lean:100)
#print axioms HarmonicBalls.greenPotentialLiouvilleHolderStmt_holds
-- 2.5: an LQG clock from every start for every 0 < gamma < 2 and alpha0 < Q, and the LBM clause for it (HarmonicBalls/Proofs/Potential/LQGClockInsertedEveryStart.lean:143, :157)
#print axioms HarmonicBalls.exists_ae_forall_isLQGClock
#print axioms HarmonicBalls.exists_lbmClause
-- 11.12 corrected [C43], every insertion, every universe (HarmonicBalls/FirstPass/Phase2/CorrectedLemma11_12Derived.lean:35, :80)
#print axioms HarmonicBalls.correctedLemma11_12_zero_derived
#print axioms HarmonicBalls.correctedLemma11_12_derived
-- 11.18 for every geometry of concentric disks, conditioning modulo additive constants (HarmonicBalls/Proofs/Sec11/MassDiamPositive.lean:59)
#print axioms HarmonicBalls.massDiamModConst_holds
-- 2.5: the frozen statement together with the existence of its clock family (HarmonicBalls/Proofs/Potential/LQGClockInsertedEveryStart.lean:184)
#print axioms HarmonicBalls.greenPotentialLiouvilleHolderStmt_holds_and_clock_exists
-- 11.18 as printed, conditioning on the field outside W0 (HarmonicBalls/Proofs/Sec11/MassDiamFullField.lean:217)
#print axioms HarmonicBalls.massDiamPositive_holds
-- 11.13 printed form with no hypothesis; every-xi and canonical-exponent forms (HarmonicBalls/FirstPass/Phase2/ForallXiCanonicalEquivalence.lean:35, :45, :58, :66)
#print axioms HarmonicBalls.manyPinchScales_derived
#print axioms HarmonicBalls.harmonicBallNotMetricBallStmt_iff_canonical
#print axioms HarmonicBalls.harmonicBallNoveltyStmt_iff_canonical
#print axioms HarmonicBalls.correctedLemma11_13Canonical_of_corrected
-- 1.1 test class with signed Radon measures (HarmonicBalls/Proofs/Potential/GreenPotentialClassSupport.lean:42); 11.1 with rotations (HarmonicBalls/Proofs/Sec11/LipschitzDomainRotation.lean:30)
#print axioms HarmonicBalls.radonGreenPotentialClass_eq
#print axioms HarmonicBalls.isLipschitzDomain_iff_rotation
-- 1.1 test class with support closed relative to O (HarmonicBalls/Proofs/Potential/GreenPotentialClassRelativeSupport.lean)
#print axioms HarmonicBalls.greenPotentialClass_subset_relGreenPotentialClass
#print axioms HarmonicBalls.IsHarmonicBallGen.lintegral_greenPotentialENN_relative
#print axioms HarmonicBalls.IsHarmonicBallGen.hasMeanValueProperty_relative
#print axioms HarmonicBalls.isHarmonicBallGen_iff_rel
#print axioms HarmonicBalls.isHarmonicBallGen_eq_rel
-- 2.5: the clock from every start on one field event, strictly increasing from zero to infinity, with speed measure mu_h (HarmonicBalls/Proofs/Potential/LQGClockStrictEveryStart.lean)
#print axioms HarmonicBalls.exists_ae_forall_isLQGClock_isTimeChangeClock
-- 2.6: the input (13.1) of Kigami's Theorem 13.1 for every square, and its composition with the cited theorem (HarmonicBalls/Proofs/Potential/SquareClippedBallVolume.lean)
#print axioms HarmonicBalls.ae_forall_closedSquare_volume_bounds
#print axioms HarmonicBalls.ae_forall_closedSquare_kigamiVolumeBounds
#print axioms HarmonicBalls.ae_forall_closedSquare_heatKernel_of_kigami
-- 2.6: scaling from the unit square, and the reduction to the clock identification and positivity (HarmonicBalls/Proofs/Potential/ReflectedSquareScaling.lean)
#print axioms HarmonicBalls.reflectedPlanarBrownianMotion_map_unitSquarePathChart
#print axioms HarmonicBalls.isLBMHeatKernel_of_unitSquare
#print axioms HarmonicBalls.reflectedLBMHeatKernel_of_identification
-- 2.6 clock identification, step 1: fold invariance and the Markov transfer of reflected Brownian motion (HarmonicBalls/Proofs/Potential/ReflectedBrownianFoldInvariance.lean)
#print axioms HarmonicBalls.reflectedPlanarBrownianMotion_zero_one_squareFold
#print axioms HarmonicBalls.ae_reflected_shift_of_ae_ref
-- 2.6 clock identification, step 2: one measurable clock equal to the per-start limits from every start (HarmonicBalls/Proofs/Potential/UniversalClock.lean)
#print axioms HarmonicBalls.ae_tendsto_of_tendstoClockInMeasure
#print axioms HarmonicBalls.exists_universal_clock
#print axioms HarmonicBalls.IsApproxClocks.ae_eq_of_shift_zero
-- 2.6 clock identification, step 3: the LQG clocks of a square as one clock of reflected Brownian motion in the unit square (HarmonicBalls/Proofs/Potential/ReflectedClockIdentification.lean)
#print axioms HarmonicBalls.exists_unitSquare_clock_of_isLQGClock
#print axioms HarmonicBalls.measurable_lqgClockApprox_pathNaturalFiltration
#print axioms HarmonicBalls.exists_isUnitSquarePCAF_of_isLQGClock
-- 2.6 clock identification, step 4: Lebesgue measure on the unit square is invariant for reflected Brownian motion (HarmonicBalls/Proofs/Potential/ReflectedLebesgueInvariance.lean)
#print axioms HarmonicBalls.intervalIntegral_unitIntervalFold_add_add_sub
#print axioms HarmonicBalls.setIntegral_integral_planarGaussian_squareFold
#print axioms HarmonicBalls.lintegral_reflectedPlanarBrownianMotion_eval_mem
#print axioms HarmonicBalls.lintegral_lintegral_reflectedPlanarBrownianMotion_eval
-- 2.6 clock identification, step 5: Markov property at fixed times and second moments of occupation integrals (HarmonicBalls/Proofs/Potential/ReflectedBrownianMarkov.lean)
#print axioms HarmonicBalls.lintegral_reflected_eval_mul_shift
#print axioms HarmonicBalls.lintegral_windowOccupation_sq_le
-- 2.6 clock identification, step 6: Green potentials of reflected Brownian motion (HarmonicBalls/Proofs/Potential/ReflectedGreenPotentialBound.lean)
#print axioms HarmonicBalls.lintegral_gaussianReal_unitIntervalFold_le
#print axioms HarmonicBalls.lintegral_planarGaussian_squareFold_le
#print axioms HarmonicBalls.lintegral_windowOccupation_reflected_le
-- 2.6 clock identification, step 7: the Revuz formula (HarmonicBalls/Proofs/Potential/ReflectedRevuzFormula.lean)
#print axioms HarmonicBalls.lintegral_unitSquareRevuzMeasure_of_isUnitSquarePCAF
#print axioms HarmonicBalls.tendstoInMeasure_integral_clockOccupationMeasure
#print axioms HarmonicBalls.clockStieltjesFunction_measure_restrict_of_density
-- 2.6 clock identification, step 8: Revuz measure of a limit of clocks with densities (HarmonicBalls/Proofs/Potential/ReflectedRevuzIdentification.lean)
#print axioms HarmonicBalls.unitSquareRevuzMeasure_eq_of_density_clocks
-- 2.6 clock identification, step 9: the Revuz measure of the LQG clock, and Proposition 2.6 up to positivity (HarmonicBalls/Proofs/Potential/ReflectedLQGRevuzMeasure.lean)
#print axioms HarmonicBalls.IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero_of_pos
#print axioms HarmonicBalls.tendsto_setLIntegral_of_tendsto_integral
#print axioms HarmonicBalls.transportedClockApprox_eq_integral
#print axioms HarmonicBalls.exists_green_bound_unitSquareClockDensity
#print axioms HarmonicBalls.ae_exists_isUnitSquarePCAF_revuz_eq
#print axioms HarmonicBalls.reflectedLBMHeatKernel_of_kigami_of_positivity
