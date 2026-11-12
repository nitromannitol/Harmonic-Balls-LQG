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
import HarmonicBalls.FirstPass.Phase2.DerivedInputs42
import HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer
import HarmonicBalls.Proofs.Sec6.FullThreeInputAssembly
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences
import HarmonicBalls.Proofs.Sec9.ObstacleComparison
import HarmonicBalls.Steps.Sec2.VolumeGrowth

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
-- 11.12: firstPass_11_12 (HarmonicBalls/FirstPass/S11e.lean:42)
#print axioms HarmonicBalls.firstPass_11_12
-- 11.13: manyPinchScales_of_corrected (HarmonicBalls/FirstPass/Closure/Bridge12.lean:322)
#print axioms HarmonicBalls.Closure.manyPinchScales_of_corrected
-- 11.14: closure_11_14 (HarmonicBalls/FirstPass/Closure/Sec11.lean:139)
#print axioms HarmonicBalls.Closure.closure_11_14
-- 11.15: firstPass_11_15_derivedInputs3 (HarmonicBalls/FirstPass/Phase2/DerivedInputs3.lean:945)
#print axioms HarmonicBalls.firstPass_11_15_derivedInputs3
-- 11.16: firstPass_11_16_of_11_17 (HarmonicBalls/FirstPass/S11e.lean:29)
#print axioms HarmonicBalls.firstPass_11_16_of_11_17
-- 11.16: firstPass_11_16_corrected_derivedInputs39 (HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:97)
#print axioms HarmonicBalls.firstPass_11_16_corrected_derivedInputs39
-- 11.16 audit row: firstPass_11_16_corrected_derivedInputs (HarmonicBalls/FirstPass/Phase2/DerivedInputs31.lean:24)
#print axioms HarmonicBalls.firstPass_11_16_corrected_derivedInputs
-- 11.17 corrected form: firstPass_11_17_corrected_derivedInputs38 (HarmonicBalls/FirstPass/Phase2/DerivedInputs38.lean:75)
#print axioms HarmonicBalls.firstPass_11_17_corrected_derivedInputs38
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
