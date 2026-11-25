# Axiom gate: kernel axioms of the numbered results

Owner: worker z3 (task fp-clean-d6-axiom-gate, item D6 of the clean-up, lead decision R61). Checked at repository HEAD b01b9b8c with `checks/AxiomGate.lean` (lc, lock-free; built .olean files; uncommitted working-tree edits are not part of the check unless built).

**Reproduce.** `lc checks/AxiomGate.lean` (or `lake env lean checks/AxiomGate.lean` from the repository root). The file is outside the default library: it is not built by `lake build`, and it is never edited by the lakefile.

**What is checked.** One `#print axioms` line per declaration: the counted declaration of each numbered result (one per result, COUNTED-MANIFEST.md), the forall-xi and canonical-xi forms, the Proofs-only results, and the theorems of DERIVED rows (PHASE2-DERIVATION-STATUS.md). `#print axioms` reports the kernel axioms used, including `sorryAx`.

**What it does not show.** `#print axioms` does not list hypotheses. A declaration that depends only on `propext`, `Classical.choice`, `Quot.sound` can still be conditional: its explicit binders (literature Props such as `hDG`, `hCC`, `hE`, or frozen inputs) are part of its signature. The binder columns of COUNTED-MANIFEST.md and the remaining-input column of PHASE2-DERIVATION-STATUS.md give that information. "Standard axioms only" therefore means "no extra axiom", not "unconditional".

**Result.** 225 declarations (rechecked 2026-11-12 07:20 UTC at the Lattice-Probability pin b73eebb; the 53 added after the 172 are the round-43 forms of DerivedInputs43.lean; of the 172, the 2 added after the 170 are the closed-square form of Lemma 11.10 and the field-axioms form of Proposition 11.9; of the 170, the 3 added after the first 167 are the round-42 forms of DerivedInputs42.lean and the Weyl-shifted-sup form of Lemma 11.10; the 42 added are the round-41 forms of DerivedInputs41.lean, listed at the end of the gate), all with axiom output (0 missing). The first run of this gate had 92; the updates below record the additions. 0 declarations use an axiom beyond `propext`, `Classical.choice`, `Quot.sound`.

Distinct axiom sets over all declarations: 225 with [propext, Classical.choice, Quot.sound].

**Update 2026-11-11 (round-36 counted forms).** `checks/AxiomGate.lean` now has 112 `#print axioms` lines: 11 were added for the `_derivedInputs36` counted forms of 1.3, 5.2, 5.3, 5.4, 5.5, 7.2, 8.1, 8.2, 9.2, 10.7, 11.6 (`HarmonicBalls/FirstPass/Phase2/DerivedInputs36.lean`; COUNTED-MANIFEST.md, round-36 refresh), in which the input `PhaseTorusDoublingProductErgodicFrozen` is supplied by a theorem. All 112 declarations print [propext, Classical.choice, Quot.sound]. The tables below are as of the earlier check and still name the previous counted forms of those results.

**Update 2026-11-24.** `checks/AxiomGate.lean` has 267 `#print axioms` lines. The seven added last print the every-ξ forms `correctedLemma11_13_forallXi_derived`, `firstPass_11_11_forallXi_derived`, `firstPass_1_2_forallXi_derived` and the Weyl exponent `xi_eq_xiGamma_derived` (`HarmonicBalls/FirstPass/Phase2/WeylExponentOfDG20.lean`), and the canonical-exponent forms `correctedLemma11_13Canonical_derived`, `harmonicBallNotMetricBallCanonical_derived`, `harmonicBallNoveltyCanonical_derived` (`HarmonicBalls/FirstPass/Phase2/LocalMetricReplacementDerivedCanonical.lean`); each has no binder and prints [propext, Classical.choice, Quot.sound] (checked with their two modules built at Lattice-Probability 10ba33c4).

**Update 2026-11-24 (Propositions 2.5, Lemmas 11.12 and 11.18).** `checks/AxiomGate.lean` has 272 `#print axioms` lines. The six added last print `greenPotentialLiouvilleHolderStmt_holds` (the frozen Proposition 2.5 at every universe), `exists_ae_forall_isLQGClock` and `exists_lbmClause` (an LQG clock from every start for every 0 < γ < 2 and α₀ < Q, and the LBM clause of Proposition 2.5 for it), `correctedLemma11_12_zero_derived` and `correctedLemma11_12_derived` (the corrected Lemma 11.12 for every insertion, at universe 0 and at every universe) and `massDiamModConst_holds` (Lemma 11.18 for every geometry of concentric disks). All 272 declarations print [propext, Classical.choice, Quot.sound]. Eight further lines (280 in all) print `greenPotentialLiouvilleHolderStmt_holds_and_clock_exists`, `massDiamPositive_holds` (11.18 as printed), `manyPinchScales_derived`, `harmonicBallNotMetricBallStmt_iff_canonical`, `harmonicBallNoveltyStmt_iff_canonical`, `correctedLemma11_13Canonical_of_corrected`, `radonGreenPotentialClass_eq` and `isLipschitzDomain_iff_rotation`. Five further lines (285 in all; log 1125-011246-446489, all standard) print `greenPotentialClass_subset_relGreenPotentialClass`, `IsHarmonicBallGen.lintegral_greenPotentialENN_relative`, `IsHarmonicBallGen.hasMeanValueProperty_relative`, `isHarmonicBallGen_iff_rel` and `isHarmonicBallGen_eq_rel` (the test class of Theorem 1.1 with support closed relative to O defines the same harmonic balls). One further line (286 in all; log 1125-020139-1357967, all standard) prints `exists_ae_forall_isLQGClock_isTimeChangeClock` (the clock of Proposition 2.5 from every start on one field event, strictly increasing from zero to infinity, with speed measure μ_h). Three further lines (289 in all; log 1125-023745-2140197, all standard) print `ae_forall_closedSquare_volume_bounds`, `ae_forall_closedSquare_kigamiVolumeBounds` and `ae_forall_closedSquare_heatKernel_of_kigami` (the input (13.1) of Kigami's Theorem 13.1 for the LQG measure of every square, and its composition with the cited theorem, which enters as a hypothesis). Three further lines (292 in all; log 1125-025843-2632525, all standard) print `reflectedPlanarBrownianMotion_map_unitSquarePathChart`, `isLBMHeatKernel_of_unitSquare` (the scaling from the unit square) and `reflectedLBMHeatKernel_of_identification` (Proposition 2.6 from the cited theorem, the clock identification and positivity, which enter as hypotheses).

**Not gated, by design or by status.**
- Numbered results with no declaration in `HarmonicBalls/FirstPass/` or `HarmonicBalls/Closure/` (COUNTED-MANIFEST.md, second table): 2.1, 2.2, 2.5, 2.6, 9.2, 10.5 (11.17 is gated since the round-51 refresh of COUNTED-MANIFEST.md). The manifest records no declaration for them, so nothing is gated for these results.
- Row 6 LP-stage route (`LPStage/LQGMeasureDerived.lean` and its bridge): not gated, because its staging is parked (R41). Rows 15 and 51 (LP PARTIAL): only the HB-route theorem is gated.
- Row 28 (DERIVED conditional, `weylShiftedSupMeasurable_derived`): its axioms are clean, but it is conditional on the frozen inputs `LQGMetricFieldAxiomsUnivFrozen`, `WeylScalingCompositionFrozen`, `LQGInternalMetricWeylAeMeasurableFrozen` (PHASE2-DERIVATION-STATUS.md row 28). They are hypotheses, not axioms, so this gate does not show them.
- Declarations of the counted table whose binders are named literature Props (hDG, hCC, hE, hTyp, hholder, ...): the Props are in `HarmonicBalls/Proposed/` or `HarmonicBalls/External/`, and the gate does not show them. See COUNTED-MANIFEST.md, binder columns.
- Not checked here: the `#print axioms` of `LPStage.All` (imported, no `#print` line; it was not in the requested list).

## Counted declarations: one per numbered result (COUNTED-MANIFEST.md, first table)

| label | declaration | file:line | axioms |
|---|---|---|---|
| 1.1 | `HarmonicBalls.firstPass_1_1` | `HarmonicBalls/FirstPass/S1S10.lean:35` | propext, Classical.choice, Quot.sound |
| 1.2 | `HarmonicBalls.firstPass_1_2` | `HarmonicBalls/FirstPass/S1S10.lean:43` | propext, Classical.choice, Quot.sound |
| 1.3 | `HarmonicBalls.firstPass_1_3` | `HarmonicBalls/FirstPass/S1S10.lean:53` | propext, Classical.choice, Quot.sound |
| 2.3 | `HarmonicBalls.Closure.closure_2_3` | `HarmonicBalls/FirstPass/Closure.lean:113` | propext, Classical.choice, Quot.sound |
| 3.1 | `HarmonicBalls.Closure.closure_3_1_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:125` | propext, Classical.choice, Quot.sound |
| 3.2 | `HarmonicBalls.Closure.closure_3_2_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:135` | propext, Classical.choice, Quot.sound |
| 3.3 | `HarmonicBalls.Closure.closure_3_3_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:149` | propext, Classical.choice, Quot.sound |
| 3.4 | `HarmonicBalls.Closure.closure_3_4_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:159` | propext, Classical.choice, Quot.sound |
| 3.5 | `HarmonicBalls.Closure.closure_3_5_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:172` | propext, Classical.choice, Quot.sound |
| 4.1 | `HarmonicBalls.Closure.closure_4_1_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:182` | propext, Classical.choice, Quot.sound |
| 4.2 | `HarmonicBalls.Closure.closure_4_2_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:192` | propext, Classical.choice, Quot.sound |
| 4.3 | `HarmonicBalls.Closure.closure_4_3_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:202` | propext, Classical.choice, Quot.sound |
| 5.1 | `HarmonicBalls.Closure.closure_5_1_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:212` | propext, Classical.choice, Quot.sound |
| 5.2 | `HarmonicBalls.Closure.closure_5_2_derivedInputs19` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs19.lean:82` | propext, Classical.choice, Quot.sound |
| 5.3 | `HarmonicBalls.firstPass_5_3` | `HarmonicBalls/FirstPass/S5S7S8.lean:136` | propext, Classical.choice, Quot.sound |
| 5.4 | `HarmonicBalls.firstPass_5_4` | `HarmonicBalls/FirstPass/S5S7S8.lean:148` | propext, Classical.choice, Quot.sound |
| 5.5 | `HarmonicBalls.firstPass_5_5` | `HarmonicBalls/FirstPass/S5S7S8.lean:161` | propext, Classical.choice, Quot.sound |
| 5.6 | `HarmonicBalls.Closure.closure_5_6_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:261` | propext, Classical.choice, Quot.sound |
| 5.7 | `HarmonicBalls.Closure.closure_5_7_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:270` | propext, Classical.choice, Quot.sound |
| 5.8 | `HarmonicBalls.Closure.closure_5_8_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:279` | propext, Classical.choice, Quot.sound |
| 6.1 | `HarmonicBalls.Closure.closure_6_1_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:288` | propext, Classical.choice, Quot.sound |
| 6.2 | `HarmonicBalls.Closure.closure_6_2_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:297` | propext, Classical.choice, Quot.sound |
| 6.3 | `HarmonicBalls.Closure.closure_6_3_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:306` | propext, Classical.choice, Quot.sound |
| 6.4 | `HarmonicBalls.Closure.closure_6_4_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:315` | propext, Classical.choice, Quot.sound |
| 6.6 | `HarmonicBalls.Closure.closure_6_6_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:324` | propext, Classical.choice, Quot.sound |
| 6.7 | `HarmonicBalls.Closure.closure_6_7_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:333` | propext, Classical.choice, Quot.sound |
| 6.8 | `HarmonicBalls.Closure.closure_6_8_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:342` | propext, Classical.choice, Quot.sound |
| 6.9 | `HarmonicBalls.Closure.closure_6_9_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:351` | propext, Classical.choice, Quot.sound |
| 6.10 | `HarmonicBalls.Closure.closure_6_10_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:360` | propext, Classical.choice, Quot.sound |
| 6.11 | `HarmonicBalls.Closure.closure_6_11_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:369` | propext, Classical.choice, Quot.sound |
| 6.12 | `HarmonicBalls.Closure.closure_6_12_derivedInputs38` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs38.lean:141` | propext, Classical.choice, Quot.sound |
| 6.13 | `HarmonicBalls.Closure.closure_6_13_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:378` | propext, Classical.choice, Quot.sound |
| 7.1 | `HarmonicBalls.Closure.closure_7_1_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:387` | propext, Classical.choice, Quot.sound |
| 7.2 | `HarmonicBalls.firstPass_7_2` | `HarmonicBalls/FirstPass/S5S7S8.lean:52` | propext, Classical.choice, Quot.sound |
| 8.1 | `HarmonicBalls.firstPass_8_1` | `HarmonicBalls/FirstPass/S5S7S8.lean:72` | propext, Classical.choice, Quot.sound |
| 8.2 | `HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs23` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs23.lean:226` | propext, Classical.choice, Quot.sound |
| 8.3 | `HarmonicBalls.Closure.closure_8_3` | `HarmonicBalls/FirstPass/Closure/Sec78910.lean:150` | propext, Classical.choice, Quot.sound |
| 9.3 | `HarmonicBalls.firstPass_9_3_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:57` | propext, Classical.choice, Quot.sound |
| 9.4 | `HarmonicBalls.firstPass_9_4_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:67` | propext, Classical.choice, Quot.sound |
| 10.1 | `HarmonicBalls.firstPass_10_1` | `HarmonicBalls/FirstPass/S1S10.lean:64` | propext, Classical.choice, Quot.sound |
| 10.6 | `HarmonicBalls.firstPass_10_6` | `HarmonicBalls/FirstPass/S1S10.lean:92` | propext, Classical.choice, Quot.sound |
| 10.7 | `HarmonicBalls.firstPass_10_7` | `HarmonicBalls/FirstPass/S1S10.lean:75` | propext, Classical.choice, Quot.sound |
| 11.2 | `HarmonicBalls.firstPass_11_2` | `HarmonicBalls/FirstPass/S11.lean:59` | propext, Classical.choice, Quot.sound |
| 11.5 | `HarmonicBalls.firstPass_11_5` | `HarmonicBalls/FirstPass/S11.lean:67` | propext, Classical.choice, Quot.sound |
| 11.6 | `HarmonicBalls.Closure.closure_11_6_derivedInputs19` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs19.lean:240` | propext, Classical.choice, Quot.sound |
| 11.7 | `HarmonicBalls.firstPass_11_7_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:77` | propext, Classical.choice, Quot.sound |
| 11.8 | `HarmonicBalls.Closure.closure_11_8_derivedInputs39` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs39.lean:448` | propext, Classical.choice, Quot.sound |
| 11.9 | `HarmonicBalls.firstPass_11_9_derivedInputs38` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs38.lean:62` | propext, Classical.choice, Quot.sound |
| 11.10 | `HarmonicBalls.S11c.firstPass_11_10_derivedInputs38` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs38.lean:151` | propext, Classical.choice, Quot.sound |
| 11.11 | `HarmonicBalls.firstPass_11_11` | `HarmonicBalls/FirstPass/S11.lean:111` | propext, Classical.choice, Quot.sound |
| 11.12 | `HarmonicBalls.firstPass_11_12` | `HarmonicBalls/FirstPass/S11e.lean:42` | propext, Classical.choice, Quot.sound |
| 11.13 | `HarmonicBalls.Closure.manyPinchScales_of_corrected` | `HarmonicBalls/FirstPass/Closure/Bridge12.lean:322` | propext, Classical.choice, Quot.sound |
| 11.14 | `HarmonicBalls.Closure.closure_11_14` | `HarmonicBalls/FirstPass/Closure/Sec11.lean:139` | propext, Classical.choice, Quot.sound |
| 11.15 | `HarmonicBalls.firstPass_11_15_derivedInputs3` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs3.lean:945` | propext, Classical.choice, Quot.sound |
| 11.16 | `HarmonicBalls.firstPass_11_16_of_11_17` | `HarmonicBalls/FirstPass/S11e.lean:29` | propext, Classical.choice, Quot.sound |
| 11.17 | `HarmonicBalls.pinchThirdEventPositiveStmt_derivedInputsMetric` | `HarmonicBalls/FirstPass/Phase2/LQGMetricXiPos.lean:233` | propext, Classical.choice, Quot.sound |
| A.1 | `HarmonicBalls.Closure.closure_A_1` | `HarmonicBalls/FirstPass/Closure/SecA45.lean:37` | propext, Classical.choice, Quot.sound |
| A.2 | `HarmonicBalls.Closure.closure_A_2` | `HarmonicBalls/FirstPass/Closure/SecA45.lean:40` | propext, Classical.choice, Quot.sound |
| A.3 | `HarmonicBalls.Closure.closure_A_3` | `HarmonicBalls/FirstPass/Closure/SecA45.lean:43` | propext, Classical.choice, Quot.sound |
| A.4 | `HarmonicBalls.Closure.closure_A_4` | `HarmonicBalls/FirstPass/Closure/SecA45.lean:46` | propext, Classical.choice, Quot.sound |
| A.5 | `HarmonicBalls.Closure.closure_A_5` | `HarmonicBalls/FirstPass/Closure/SecA45.lean:49` | propext, Classical.choice, Quot.sound |
| A.6 | `HarmonicBalls.Closure.closure_A_6` | `HarmonicBalls/FirstPass/Closure/SecA45.lean:52` | propext, Classical.choice, Quot.sound |

## Forall-xi and canonical-xi forms (COUNTED-MANIFEST.md)

| label | declaration | file:line | axioms |
|---|---|---|---|
| 1.2 forall-xi `HarmonicBallNoveltyStmt` | `HarmonicBalls.firstPass_1_2` | `HarmonicBalls/FirstPass/S1S10.lean:43` | propext, Classical.choice, Quot.sound |
| 11.11 forall-xi `HarmonicBallNotMetricBallStmt` | `HarmonicBalls.firstPass_11_11` | `HarmonicBalls/FirstPass/S11.lean:111` | propext, Classical.choice, Quot.sound |
| 11.13 forall-xi `CorrectedLemma11_13Stmt` | `HarmonicBalls.correctedLemma11_13_of_identity` | `HarmonicBalls/FirstPass/S11i/Assembly13.lean:79` | propext, Classical.choice, Quot.sound |
| 1.2 canonical-xi `HarmonicBallNoveltyCanonicalStmt` | `HarmonicBalls.harmonicBallNoveltyStmt_of_existence_and_results_canonical` | `HarmonicBalls/FirstPass/Canonical/Novelty.lean:23` | propext, Classical.choice, Quot.sound |
| 11.11 canonical-xi `HarmonicBallNotMetricBallCanonicalStmt` | `HarmonicBalls.harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth` | `HarmonicBalls/FirstPass/Canonical/NotMetricBall.lean:129` | propext, Classical.choice, Quot.sound |
| 11.13 canonical-xi `CorrectedLemma11_13CanonicalStmt` | `HarmonicBalls.firstPass_11_13_canonical` | `HarmonicBalls/FirstPass/S11i/Corrected11_13.lean:127` | propext, Classical.choice, Quot.sound |

## Numbered results whose only declaration is in Proofs/ (COUNTED-MANIFEST.md)

| label | declaration | file:line | axioms |
|---|---|---|---|
| 2.4 | `HarmonicBalls.liouvilleVolumeGrowthStmt_of_existence` | `HarmonicBalls/Proofs/Sec9/LQGExistenceConsequences.lean:30` | propext, Classical.choice, Quot.sound |
| 6.5 | `HarmonicBalls.Section6Full.annulusIterationStmt_of_three_inputs` | `HarmonicBalls/Proofs/Sec6/FullThreeInputAssembly.lean:73` | propext, Classical.choice, Quot.sound |
| 9.1 | `HarmonicBalls.obstacleComparison` | `HarmonicBalls/Proofs/Sec9/ObstacleComparison.lean:32` | propext, Classical.choice, Quot.sound |

## Derived-input theorems of DERIVED rows (PHASE2-DERIVATION-STATUS.md)

| label | declaration | file:line | axioms |
|---|---|---|---|
| row 5 | `HarmonicBalls.Section6.lqgMeasureWeylScaling` | `HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean:124` | propext, Classical.choice, Quot.sound |
| row 6 | `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` | `HarmonicBalls/FirstPass/Phase2/ProfileDecoderDerived.lean:401` | propext, Classical.choice, Quot.sound |
| row 7 | `HarmonicBalls.birkhoffPointwiseErgodic_derived` | `HarmonicBalls/FirstPass/S8c/BirkhoffDerived.lean:21` | propext, Classical.choice, Quot.sound |
| row 10 | `HarmonicBalls.WholePlaneGFFAffineInvariance_derived` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs11.lean:26` | propext, Classical.choice, Quot.sound |
| row 11 | `HarmonicBalls.localLQGInsertionWeylOffOrigin_derived` | `HarmonicBalls/FirstPass/S8c/WeylOffOriginDerived.lean:88` | propext, Classical.choice, Quot.sound |
| row 13 | `HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived` | `HarmonicBalls/FirstPass/Phase2/DerivedInputs9.lean:37` | propext, Classical.choice, Quot.sound |
| row 13 | `HarmonicBalls.cameronMartinGFFMutualAbsCont_derived` | `HarmonicBalls/FirstPass/Phase2/CameronMartinMutualDerived.lean:56` | propext, Classical.choice, Quot.sound |
| row 15 | `HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` | `HarmonicBalls/FirstPass/Phase2/LocalDecoderCommonDerived.lean:1859` | propext, Classical.choice, Quot.sound |
| row 21 | `HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived` | `HarmonicBalls/FirstPass/Phase2/MassFunctionalDerived.lean:702` | propext, Classical.choice, Quot.sound |
| row 22 | `HarmonicBalls.lqgMeasureSquareMeasurable_derived'` | `HarmonicBalls/FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean:192` | propext, Classical.choice, Quot.sound |
| row 26 | `HarmonicBalls.weylInternalClosed_derived` | `HarmonicBalls/FirstPass/Phase2/WeylInternalClosedDerived.lean:149` | propext, Classical.choice, Quot.sound |
| row 27 | `HarmonicBalls.weylShiftedMassMeasurable_derived` | `HarmonicBalls/FirstPass/Phase2/WeylShiftedMassDerived.lean:96` | propext, Classical.choice, Quot.sound |
| row 28 | `HarmonicBalls.weylShiftedSupMeasurable_derived` | `HarmonicBalls/FirstPass/Phase2/WeylShiftedSupDerived2.lean:124` | propext, Classical.choice, Quot.sound |
| row 33 | `HarmonicBalls.lqgMassInnerMeasurable_derived'` | `HarmonicBalls/FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean:198` | propext, Classical.choice, Quot.sound |
| row 35 | `HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived` | `HarmonicBalls/FirstPass/Phase2/PlaneDomainDerived.lean:14` | propext, Classical.choice, Quot.sound |
| row 37 | `HarmonicBalls.S11aj.cameronMartinGFFReweighting_derived` | `HarmonicBalls/FirstPass/Phase2/CameronMartinReweightingDerived2.lean:267` | propext, Classical.choice, Quot.sound |
| row 39 | `HarmonicBalls.internalMetricClosedEqIInfThickening_derived` | `HarmonicBalls/FirstPass/Phase2/InternalMetricClosedDerived.lean:408` | propext, Classical.choice, Quot.sound |
| row 42 | `HarmonicBalls.lqgMetricLengthUniv_derived` | `HarmonicBalls/FirstPass/Phase2/LengthUnivDerived.lean:30` | propext, Classical.choice, Quot.sound |
| row 49 | `HarmonicBalls.lqgMeasureLocality_derived` | `HarmonicBalls/FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean:185` | propext, Classical.choice, Quot.sound |
| row 51 | `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` | `HarmonicBalls/FirstPass/Phase2/LocalDecoderCommonDerived.lean:1564` | propext, Classical.choice, Quot.sound |
| row 56 | `HarmonicBalls.weylMetricCompositionContinuousOuter_derived` | `HarmonicBalls/FirstPass/Phase2/WeylCompositionOuterDerived.lean:1221` | propext, Classical.choice, Quot.sound |
| row 57 | `HarmonicBalls.weylScaledEuclidean_derived` | `HarmonicBalls/FirstPass/Phase2/WeylScaledEuclideanDerived.lean:93` | propext, Classical.choice, Quot.sound |

Source: `checks/AxiomGate.lean` (generated by z3 from the counted manifest and the DERIVED rows; the `#print` lines are its only content besides the imports).
