# Phase 2 input status: docstring verdicts of the frozen, staged and first-pass inputs

Record of the mathematical status that the docstrings give for the frozen, staged and first-pass inputs, copied as written before any cleaning (PHASE2-CLEAN-PLAN.md, D8). Verdicts are copied, not judged here. Read-only audit by z6 (task fp-phase2-input-status, 2026-11-10); Lean sources read as committed that day (docstrings only).

- Scope: every `def` in `FirstPass/Frozen/` (17 files) and `Proposed/` (8 files), plus 8 other `def`s whose docstring says FIRST-PASS FROZEN (in FirstPass/S11r/Frozen.lean, FrozenMetricReplacement.lean, LocalMetricReplacement.lean). `HarmonicBalls/External/` does not exist. 109 defs in all: 68 in FirstPass/Frozen, 33 in Proposed, 8 elsewhere.
- Paths are relative to `HarmonicBalls/`; the line is the `def` line. Method: the `/-- -/` block directly above each `def` (attributes skipped), read by `scratch-z6/gen_status.py` (uncommitted). Eight rows were checked against the source by hand (section 4).
- Status: TRUE; FALSE AS TYPED; RETIRED; DERIVED INTERFACE; DERIVED BRIDGE; PENDING; or `other: "..."` (five words of the docstring, when it has no verdict word). `(truth: X)` is the verdict the docstring gives beside a structural label. `→` gives the replacement or derivation the docstring names; "no name given" means it names none.
- Evidence: the first three references in the docstring (chat N, notes/ path, operator time, Codex, ChatGPT time). Literature locator: author, arXiv id, theorem or proposition, page, as the docstring writes them; `none` if absent.
- `*`: input of a counted declaration (PHASE2-INVENTORY.md section 2). 49 of its 57 inputs are in this table; the other 8 are Draft or own-result inputs.

## 1. Counts

| status (primary) | rows | of which truth FALSE AS TYPED | of which truth TRUE |
|---|---|---|---|
| TRUE | 42 | 0 | 42 |
| FALSE AS TYPED | 1 | 1 | 0 |
| RETIRED | 13 | 6 | 2 |
| DERIVED INTERFACE | 9 | 0 | 9 |
| DERIVED BRIDGE | 0 | - | - |
| PENDING | 2 | 0 | 0 |
| other | 42 | 0 | 0 |
| NO DOCSTRING | 0 | 0 | 0 |

All verdict words in the table: TRUE 53, FALSE AS TYPED 7, none 49. Structural labels: RETIRED 13, DERIVED INTERFACE 9.

## 2. FALSE AS TYPED, AMBIGUOUS and PENDING rows (read first)

| # | Name | file:line | status | evidence | literature locator |
|---|---|---|---|---|---|
| 1 | `WeylShiftedSupMeasurableFrozen`* | FirstPass/Frozen/S11c.lean:217 | PENDING | - | Fact 2.2 |
| 2 | `WeylShiftedMassMeasurableFrozen`* | FirstPass/Frozen/S11c.lean:233 | DERIVED: `weylShiftedMassMeasurable_derived` (HarmonicBalls/FirstPass/Phase2/WeylShiftedMassDerived.lean:96, commit 5f327308; binders: none); docstring verdict was: PENDING | - | Fact 2.1 |
| 3 | `LQGInternalMetricWeylMeasurableFrozen` | FirstPass/Frozen/S11d.lean:110 | RETIRED (truth: FALSE AS TYPED) → use LQGInternalMetricWeylAeMeasurableFrozen | notes/fp-gaps/CHATGPT-hb-distribution-frozen.md; ChatGPT 02:36 UTC | Gwynne-Miller, p. 6 |
| 4 | `LQGInternalMetricContinuousFrozen` | FirstPass/Frozen/S11g.lean:45 | RETIRED (truth: FALSE AS TYPED) → no name given | operator 21:18 UTC | Bou-Rabee-Gwynne, arXiv:2208.11795, Fact 2.2 |
| 5 | `LQGMetricLengthIdentityFrozen` | FirstPass/Frozen/S11g.lean:58 | RETIRED (truth: FALSE AS TYPED) → no name given | operator 21:18 UTC | Bou-Rabee-Gwynne, arXiv:2208.11795, Fact 2.2 |
| 6 | `DMSLemmaA10WholePlaneMarkedSub`* | FirstPass/Frozen/S11i.lean:58 | TRUE (subcritical `0 < γ < 2` is in the statement; docstring states TRUE, ruling 2026-11-10) | chat 241; notes/fp-gaps/CHATGPT-241-hb-DMS-A10-marked-truth-PRO.md | Duplantier-Sheffield, arXiv:1409.7055v4, printed p. 184 |
| 7 | `CameronMartinMetricEventTransferFrozen` | FirstPass/Frozen/S11j.lean:43 | FALSE AS TYPED → superseded by CameronMartinMetricEventTransferMeasurableFrozen | notes/fp-gaps/CHATGPT-CM-metric-truth.md; notes/fp-gaps/CHATGPT-hb-frozen-truth-S11r-S11j.md | Miller-Sheffield, arXiv:1302.4738v2, Proposition 2.9, p. 49 |
| 8 | `WeylMetricCompositionFrozen` | FirstPass/Frozen/S11j.lean:91 | RETIRED (truth: FALSE AS TYPED) → superseded by WeylMetricCompositionContinuousOuterFrozen | notes/fp-gaps/CHATGPT-n4-frozen-truth-weyl.md; notes/fp-gaps/CHATGPT-hb-frozen-truth-S11r-S11j.md; ChatGPT 01:17 UTC | arXiv:2208.11795, Fact 2.2, p. 6 |
| 9 | `LocalLQGMetricNormalizedMeasurableFrozen` | FirstPass/S11r/Frozen.lean:61 | RETIRED (truth: FALSE AS TYPED) → superseded by LocalLQGMetricNormalizedMeasurableFixedMetricFrozen | ChatGPT 01:48 UTC | Gwynne-Miller, arXiv:1905.00383v3, Theorem 1.2, p. 6 |
| 10 | `LocalMarkedRootingIdentityFrozen` | FirstPass/S11r/FrozenMetricReplacement.lean:38 | RETIRED (truth: FALSE AS TYPED) → superseded by LocalMarkedRootingIdentityWeightedFrozen | ChatGPT 01:48 UTC | Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Proposition 1.1, printed p. 184 |

## 3. All rows

| # | Name | file:line | status | evidence | literature locator |
|---|---|---|---|---|---|
| 1 | `CameronMartinGFFReweighting`* | FirstPass/Frozen/S11aj.lean:33 | DERIVED INTERFACE (truth: TRUE) | chat 179; chat 151; notes/fp-gaps/CHATGPT-lh-R7-cameron-martin.md | Miller-Sheffield, arXiv:1302.4738v2, Proposition 2.9, printed p. 49 |
| 2 | `OriginRootedConeFrequencyFrozen` | FirstPass/Frozen/S11b.lean:32 | RETIRED → replaced by the internal ergodic argument of FirstPass/S11c.lean (no name) | operator 23:12 UTC | Lemma 11.7 |
| 3 | `RootedConeFrequencyTransferFrozen` | FirstPass/Frozen/S11b.lean:55 | RETIRED → replaced by the local Palm transfer in FirstPass/Frozen/S11c.lean (no name) | operator 23:12 UTC | Lemma 11.7 |
| 4 | `weylShiftPair` | FirstPass/Frozen/S11c.lean:23 | other: "The Weyl shift of an" | - | none |
| 5 | `enlargedDyadicCell` | FirstPass/Frozen/S11c.lean:30 | other: "The enlargement Ŝ of the" | - | Lemma 11.10 |
| 6 | `DyadicCellDiamSmallFrozen`* | FirstPass/Frozen/S11c.lean:67 | TRUE | notes/fp-gaps/CHATGPT-11-7-11-10-statement-audit.md; notes/fp-gaps/CHATGPT-hb-frozen-batch.md | arXiv:1905.00380v2, Proposition 3.10, p. 34 |
| 7 | `IsClosedRectangle` | FirstPass/Frozen/S11c.lean:80 | other: "A closed axis-parallel rectangle [a₁,a₂]" | - | none |
| 8 | `ConnectedSquareUnionDiamFiniteFrozen`* | FirstPass/Frozen/S11c.lean:91 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Lemma 11.10, p. 34 |
| 9 | `LQGMetricSupMeasurableFrozen`* | FirstPass/Frozen/S11c.lean:105 | other: "operator ruling, FIRST PASS wave" | - | Lemma 11.10 |
| 10 | `LQGMeasureSquareMeasurableFrozen`* | FirstPass/Frozen/S11c.lean:117 | DERIVED: `lqgMeasureSquareMeasurable_derived` (HarmonicBalls/FirstPass/Phase2/SquareMeasurableDerived.lean:37, commit 7ba20277; binders: hmeasure: Proposed LQGMeasureLocality (universal form)); docstring verdict was: other: "operator ruling, FIRST PASS wave" | - | Fact 2.1 |
| 11 | `LQGMeasureSquarePositiveFrozen`* | FirstPass/Frozen/S11c.lean:130 | TRUE; DERIVED for every model (2026-11-12): `lqgMeasureSquarePositiveFrozen_holds` (FirstPass/Phase2/SquarePositiveHolds.lean, `lqgMeasureSquarePositiveFrozen_derived` with `wholePlaneLQGBallMassBounds_holds`, `lqgMeasureCoordChange_zero_holds`, `lqgMeasureExistence_forall_field`); supplied in the closed-square form of Lemma 11.10 by `S11c.firstPass_11_10_derivedInputsSquarePositive` (FirstPass/Phase2/SquarePositiveCountedForms.lean) | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Rhodes-Vargas, arXiv:1305.6221v1, Theorem 2.12., p. 11 |
| 12 | `CameronMartinEventTransferFrozen`* | FirstPass/Frozen/S11c.lean:149 | other: "truth check: the shifted event" | - | arXiv:1302.4738v2, Lemma 11.10 |
| 13 | `WeylInternalClosedFrozen`* | FirstPass/Frozen/S11c.lean:180 | DERIVED: `weylInternalClosed_derived` (HarmonicBalls/FirstPass/Phase2/WeylInternalClosedDerived.lean:149, commit 3ec79df9; binders: none); docstring verdict was: TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Gwynne-Miller, arXiv:1905.00383v3, Fact 2.2, p. 5 |
| 14 | `WeylShiftedSupMeasurableFrozen`* | FirstPass/Frozen/S11c.lean:217 | PENDING | - | Fact 2.2 |
| 15 | `WeylShiftedMassMeasurableFrozen`* | FirstPass/Frozen/S11c.lean:233 | DERIVED: `weylShiftedMassMeasurable_derived` (HarmonicBalls/FirstPass/Phase2/WeylShiftedMassDerived.lean:96, commit 5f327308; binders: none); docstring verdict was: PENDING | - | Fact 2.1 |
| 16 | `campbellMarkedObs` | FirstPass/Frozen/S11c.lean:244 | other: "The marked restriction observation (z," | - | none |
| 17 | `campbellReferenceObs` | FirstPass/Frozen/S11c.lean:251 | other: "The reference observation at a" | - | none |
| 18 | `LocalCampbellMarkedRestrictionFrozen`* | FirstPass/Frozen/S11c.lean:268 | other: "EXTERNAL local rooted-field (Campbell–Palm) absolute" | - | Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma 11.7 |
| 19 | `WholePlaneGFFTranslationModConstFrozen` | FirstPass/Frozen/S11c.lean:292 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma 4.2, p. 16 |
| 20 | `LocalCircleAverageMeanZeroApproxFrozen` | FirstPass/Frozen/S11c.lean:313 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Duplantier-Sheffield, arXiv:0808.1560v2, Proposition 3.1, p. 3 |
| 21 | `localMeanZeroObs` | FirstPass/Frozen/S11c.lean:324 | other: "The local mean-zero observation of" | - | none |
| 22 | `rootedCircleAverage` | FirstPass/Frozen/S11c.lean:330 | other: "The circle averages of the" | - | none |
| 23 | `rootedMeanZeroObs` | FirstPass/Frozen/S11c.lean:335 | other: "The mean-zero observation of the" | - | none |
| 24 | `LocalLQGDecoderFrozen` | FirstPass/Frozen/S11c.lean:359 | TRUE | notes/fp-gaps/CHATGPT-decoder-truth.md | arXiv:0808.1560v2, Lemma 11.7 |
| 25 | `LocalLQGDecoderCommonFrozen`* | FirstPass/Frozen/S11c.lean:388 | DERIVED INTERFACE (truth: TRUE) | chat 179; notes/fp-gaps/CHATGPT-11-7-G1-G2-Q1.md; operator 22:33 UTC | Duplantier-Sheffield, arXiv:0808.1560v2, Proposition 1.1 |
| 26 | `CameronMartinLocallyLipschitzShiftAbsCont`* | FirstPass/Frozen/S11c.lean:414 | TRUE | notes/fp-gaps/CHATGPT-11-7-G1-G2-Q1.md; operator 22:33 UTC | arXiv:1302.4738v2, Proposition 2.9 |
| 27 | `PlaneDomainMinusConvexCompactPreconnectedFrozen`* | FirstPass/Frozen/S11d.lean:26 | DERIVED: `planeDomainMinusConvexCompactPreconnected_derived` (HarmonicBalls/FirstPass/Phase2/PlaneDomainDerived.lean:14, commit e99fef25; binders: none); docstring verdict was: TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Corollary 3.45, p. 255 |
| 28 | `LQGMetricContinuousShiftFactI`* | FirstPass/Frozen/S11d.lean:34 | other: "Fact 2.2 I for the" | - | Gwynne-Miller, arXiv:2208.11795, Fact 2.2, p. 6 |
| 29 | `LQGMetricContinuousShiftLocality` | FirstPass/Frozen/S11d.lean:53 | TRUE | notes/fp-gaps/CHATGPT-hb-distribution-frozen.md | Gwynne-Miller, arXiv:2208.11795, Fact 2.2, p. 6 |
| 30 | `CameronMartinGFFMutualAbsCont`* | FirstPass/Frozen/S11d.lean:74 | TRUE | notes/fp-gaps/CHATGPT-truth-new-frozen.md; notes/fp-gaps/CHATGPT-resolve-unclear.md; notes/fp-gaps/CHATGPT-11-15-17-chain-audit.md | Proposition 2.9 |
| 31 | `WeylScalingCompositionFrozen`* | FirstPass/Frozen/S11d.lean:91 | DERIVED INTERFACE (truth: TRUE) | chat 179; notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Gwynne-Miller, arXiv:1905.00383v3, Fact 2.2, p. 6 |
| 32 | `LQGInternalMetricWeylMeasurableFrozen` | FirstPass/Frozen/S11d.lean:110 | RETIRED (truth: FALSE AS TYPED) → use LQGInternalMetricWeylAeMeasurableFrozen | notes/fp-gaps/CHATGPT-hb-distribution-frozen.md; ChatGPT 02:36 UTC | Gwynne-Miller, p. 6 |
| 33 | `LQGInternalMetricWeylAeMeasurableFrozen`* | FirstPass/Frozen/S11d.lean:130 | DERIVED INTERFACE (truth: TRUE) | chat 179; notes/fp-gaps/CHATGPT-truth-1935.md; notes/fp-gaps/CHATGPT-11-15-17-chain-audit.md | Bou-Rabee-Gwynne, arXiv:2208.11795, Fact 2.2, p. 6 |
| 34 | `LQGMassFunctionalMeasurableFrozen`* | FirstPass/Frozen/S11d.lean:155 | DERIVED INTERFACE (truth: TRUE) | chat 179; notes/fp-gaps/CHATGPT-hb-distribution-frozen.md | Duplantier-Sheffield, arXiv:0808.1560v2, Fact 2.1, p. 9 |
| 35 | `LQGMetricPointwiseAEMeasurableFrozen` | FirstPass/Frozen/S11e.lean:27 | DERIVED: `lqgMetricPointwiseAEMeasurable_derived` (HarmonicBalls/FirstPass/Phase2/SquareMeasurableDerived.lean:57, commit 7ba20277; binders: hFA: Proposed LQGMetricFieldAxioms (universal form)); docstring verdict was: TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Gwynne-Miller, arXiv:2208.11795, Fact 2.2, p. 6 |
| 36 | `DDDFSquareDiameterTailFrozen` | FirstPass/Frozen/S11f.lean:34 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | arXiv:1905.00380v2, Lemma 3.19, p. 45 |
| 37 | `LQGMetricSatisfiesAxiomsUnivFrozen` | FirstPass/Frozen/S11g.lean:31 | TRUE | notes/fp-gaps/CHATGPT-hb-distribution-frozen.md | Gwynne-Pfeffer-Sun, arXiv:1905.00380, Fact 2.2, p. 6 |
| 38 | `LQGInternalMetricContinuousFrozen` | FirstPass/Frozen/S11g.lean:45 | RETIRED (truth: FALSE AS TYPED) → no name given | operator 21:18 UTC | Bou-Rabee-Gwynne, arXiv:2208.11795, Fact 2.2 |
| 39 | `LQGMetricLengthIdentityFrozen` | FirstPass/Frozen/S11g.lean:58 | RETIRED (truth: FALSE AS TYPED) → no name given | operator 21:18 UTC | Bou-Rabee-Gwynne, arXiv:2208.11795, Fact 2.2 |
| 40 | `LQGInternalMetricContinuousAlphaGFFFrozen` | FirstPass/Frozen/S11g.lean:100 | other: "truth check 21:18 UTC, notes/fp-gaps/CHATGPT-frozen-truth-2300.md:" | notes/fp-gaps/CHATGPT-frozen-truth-2300.md | Falconet-Gwynne-Pfeffer-Sun, arXiv:2208.11795, Fact 2.2, p. 10 |
| 41 | `LQGMetricLengthIdentityAlphaGFFFrozen` | FirstPass/Frozen/S11g.lean:116 | other: "truth check 21:18 UTC, minimal" | notes/fp-gaps/CHATGPT-frozen-truth-2300.md | Gwynne-Miller, arXiv:2208.11795, Fact 2.2, p. 6 |
| 42 | `InternalMetricClosedEqIInfThickeningFrozen`* | FirstPass/Frozen/S11g.lean:132 | TRUE | notes/fp-gaps/CHATGPT-K1-proof-z4-F4.md; notes/fp-gaps/CHATGPT-frozen-truth-S4d-S11g.md | none |
| 43 | `WeylScaledEuclideanFrozen`* | FirstPass/Frozen/S11g.lean:146 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-truth-0026.md; notes/fp-gaps/CHATGPT-frozen-truth-S4d-S11g.md; ChatGPT 00:37 UTC | none |
| 44 | `CircleAverageVersionMeasurableStmt` | FirstPass/Frozen/S11i.lean:24 | RETIRED → derived from IsWholePlaneGFF.ae_continuousOn_circle (no theorem name) | - | none |
| 45 | `DMSLemmaA10WholePlaneMarked` | FirstPass/Frozen/S11i.lean:42 | TRUE | chat 170; chat 241; notes/fp-gaps/CHATGPT-n3-marked-A10.md | Duplantier-Sheffield, arXiv:1409.7055v4, p. 184 |
| 46 | `DMSLemmaA10WholePlaneMarkedSub`* | FirstPass/Frozen/S11i.lean:58 | TRUE (subcritical `0 < γ < 2` is in the statement; docstring states TRUE, ruling 2026-11-10) | chat 241; notes/fp-gaps/CHATGPT-241-hb-DMS-A10-marked-truth-PRO.md | Duplantier-Sheffield, arXiv:1409.7055v4, printed p. 184 |
| 47 | `CameronMartinMetricEventTransferFrozen` | FirstPass/Frozen/S11j.lean:43 | FALSE AS TYPED → superseded by CameronMartinMetricEventTransferMeasurableFrozen | notes/fp-gaps/CHATGPT-CM-metric-truth.md; notes/fp-gaps/CHATGPT-hb-frozen-truth-S11r-S11j.md | Miller-Sheffield, arXiv:1302.4738v2, Proposition 2.9, p. 49 |
| 48 | `CameronMartinMetricEventTransferMeasurableFrozen` | FirstPass/Frozen/S11j.lean:61 | RETIRED → superseded by cameronMartinFieldCertificateTransfer (proved), FirstPass/S11j/CertificateTransfer.lean:35 | notes/fp-gaps/CHATGPT-CM-metric-truth.md; operator 22:44 UTC | none |
| 49 | `WeylMetricCompositionFrozen` | FirstPass/Frozen/S11j.lean:91 | RETIRED (truth: FALSE AS TYPED) → superseded by WeylMetricCompositionContinuousOuterFrozen | notes/fp-gaps/CHATGPT-n4-frozen-truth-weyl.md; notes/fp-gaps/CHATGPT-hb-frozen-truth-S11r-S11j.md; ChatGPT 01:17 UTC | arXiv:2208.11795, Fact 2.2, p. 6 |
| 50 | `LQGMetricExponentPositive` | FirstPass/Frozen/S11j.lean:105 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-truth-S11r-S11j.md; notes/fp-gaps/CHATGPT-xi-exponent-rigidity.md | Bou-Rabee-Gwynne, arXiv:2208.11795, Theorem 1.9, p. 8 |
| 51 | `WeylMetricCompositionContinuousOuterFrozen`* | FirstPass/Frozen/S11j.lean:117 | TRUE | notes/fp-gaps/CHATGPT-n4-frozen-truth-weyl.md; notes/fp-gaps/CHATGPT-hb-frozen-truth-0026.md | arXiv:2208.11795, Fact 2.2, p. 6 |
| 52 | `LQGMetricLengthUnivFrozen`* | FirstPass/Frozen/S11j.lean:133 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-truth-0026.md | Gwynne-Miller, Fact 2.2, p. 6 |
| 53 | `LQGMetricFieldAxiomsUnivFrozen`* | FirstPass/Frozen/S11j.lean:155 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-truth-0026.md; the universe wrapper is derived: `lqgMetricFieldAxiomsUnivFrozen_of_zero` (FirstPass/Phase2/FieldAxiomsUniv.lean:26) proves the `.{u}` form from the `.{0}` form (2026-11-12); DERIVED: `lqgMetricFieldAxiomsUnivFrozen_derived` (FirstPass/Phase2/FieldAxiomsDerived.lean:33), from the uniform unit-square crossing tail (`lqgMetricFieldAxiomsUnivFrozen_of_unitTail`, FirstPass/Phase2/UnitTailFieldAxioms.lean:43) and its proof `unitSquareCrossingTail_derived` (FirstPass/Phase2/UnitSquareCrossingTailDerived.lean:37) (2026-11-12) | Bou-Rabee-Gwynne, arXiv:2208.11795, Fact 2.2, p. 6 |
| 54 | `DomainMarkovConditionalPositiveFrozen`* | FirstPass/Frozen/S11k.lean:45 | DERIVED INTERFACE (truth: TRUE) | chat 179 | arXiv:1302.4738v2, Proposition 2.8, p. 48-49 |
| 55 | `LQGMassInnerMeasurableFrozen`* | FirstPass/Frozen/S11k.lean:66 | DERIVED INTERFACE (truth: TRUE) | chat 179; notes/fp-gaps/CHATGPT-e2-locality-z3-frozen.md | Bou-Rabee-Gwynne, arXiv:2208.11795v3, Fact 2.1, p. 9 |
| 56 | `LQGInternalDiamInnerMeasurableFrozen`* | FirstPass/Frozen/S11k.lean:89 | DERIVED INTERFACE (truth: TRUE) | chat 179; notes/fp-gaps/CHATGPT-e2-locality-z3-frozen.md | Bou-Rabee-Gwynne, arXiv:2208.11795v3, Fact 2.2, p. 10 |
| 57 | `LQGMetricAlphaWeylShiftLengthFrozen` | FirstPass/Frozen/S11m.lean:30 | other: "derived: lqgMetricAlphaWeylShiftLength_of_axioms (FirstPass/S11m/WeylShiftAlphaLength.lean) from LQGMetricFieldAxiomsUnivFrozen" | - | Gwynne-Miller, arXiv:1905.00383v3, Fact 2.2, p. 6 |
| 58 | `LQGCanonicalDecodersExistStmt`* | FirstPass/Frozen/S11n.lean:33 | DERIVED INTERFACE (truth: TRUE) | chat 179; notes/fp-gaps/CHATGPT-n1-B1-canonical-decoders.md; ChatGPT 23:53 UTC | Duplantier-Sheffield, arXiv:0808.1560v2, Theorem 1.2, p. 6 |
| 59 | `LQGCanonicalDecodersMeasurableExistStmt`* | FirstPass/Frozen/S11n.lean:71 | TRUE | notes/fp-gaps/CHATGPT-n3-B1-B2.md; notes/fp-gaps/CHATGPT-hb-decoders-weyl.md | Duplantier-Sheffield, arXiv:0808.1560v2, Proposition 1.1, printed p. 5 |
| 60 | `WholePlaneCircleAverageLimitFrozen` | FirstPass/Frozen/S11p.lean:29 | RETIRED (truth: TRUE) → derived: wholePlaneCircleAverageLimit_derived, FirstPass/S11u.lean:93 | notes/fp-gaps/CHATGPT-n4-circle-avg-limit.md | Duplantier-Sheffield, arXiv:0808.1560v2, Proposition 3.1, printed p. 8 |
| 61 | `LocalMetricReplacementFrozen`* | FirstPass/Frozen/S11rMetric.lean:33 | other: "Truth: no counterexample, quantifier structure" | notes/fp-gaps/CODEX-hN2-sol-20261110.md; Codex Sol 2026-11-10 | none |
| 62 | `TorhorstSimpleLoopFrozen`* | FirstPass/Frozen/S1S10.lean:21 | DERIVED: `torhorstSimpleLoopFrozen_holds` (HarmonicBalls/FirstPass/Phase2/TorhorstDerived.lean:47, commit ff3638c1; binders: none; from the Lattice-Probability theorem `LatticeProb.Topology.torhorstSimpleLoop`); docstring verdict was: TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Jolivet-Loridant-Luo, arXiv:1411.6776v1, Lemma 10.5, printed p. 6 |
| 63 | `LocalRootedFieldMeasureDomination`* | FirstPass/Frozen/S8c.lean:55 | TRUE | chat 219; notes/fp-gaps/CHATGPT-truth-new-frozen.md; notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma 8.2, p. 184 |
| 64 | `LocalLQGInsertionWeylOffOrigin`* | FirstPass/Frozen/S8c.lean:85 | RETIRED (truth: TRUE) → derived: localLQGInsertionWeylOffOrigin_derived, FirstPass/S8c/WeylOffOriginDerived.lean:88 | chat 219; notes/fp-gaps/G-8-2.md; notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma 8.2, p. 9 |
| 65 | `BirkhoffPointwiseErgodic`* | FirstPass/Frozen/S8c.lean:100 | TRUE | notes/fp-gaps/G-8-2.md; notes/fp-gaps/CHATGPT-hb-frozen-batch.md | June, Theorem 2.30., p. 44 |
| 66 | `LQGMeasureOfProfileMeasurableFrozen`* | FirstPass/Frozen/S8d.lean:33 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Sheffield, arXiv:0808.1560, Proposition 1.1, p. 1 |
| 67 | `PhaseTorusDoublingProductErgodicFrozen`* | FirstPass/Frozen/S8d.lean:58 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | PENDING (operator source check) |
| 68 | `RadonIntegralUniqueFrozen` | FirstPass/Frozen/S8d.lean:72 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-batch.md | Theorem 2.14, p. 40-41 |
| 69 | `WholePlaneGFFExistsFrozen`* | FirstPass/S11r/Frozen.lean:39 | TRUE | notes/fp-gaps/CHATGPT-hb-frozen-truth-S11r-S11j.md | Duplantier-Sheffield, arXiv:1302.4738v2, p. 46-47 |
| 70 | `LocalLQGMetricNormalizedMeasurableFrozen` | FirstPass/S11r/Frozen.lean:61 | RETIRED (truth: FALSE AS TYPED) → superseded by LocalLQGMetricNormalizedMeasurableFixedMetricFrozen | ChatGPT 01:48 UTC | Gwynne-Miller, arXiv:1905.00383v3, Theorem 1.2, p. 6 |
| 71 | `LocalLQGMetricNormalizedMeasurableFixedMetricFrozen` | FirstPass/S11r/Frozen.lean:89 | TRUE; DERIVED in every universe, no hypothesis (2026-11-12): `localLQGMetricNormalizedMeasurableFixedMetric_derived` (FirstPass/Phase2/FixedMetricDecoderUniv.lean, mixture-of-sample-spaces argument of MQ-lh-23 on `fmd_factor_point`) | notes/fp-gaps/CHATGPT-n2-frozen-corrected.md | Gwynne-Miller, arXiv:1905.00383v3, Theorem 1.2, p. 5-6 |
| 72 | `RootedPhysicalMetricContinuousAtInsertionFrozen`* | FirstPass/S11r/Frozen.lean:115 | DERIVED: `rootedPhysicalMetricContinuousAtInsertion_derived` (HarmonicBalls/FirstPass/Phase2/RootedInsertionContinuityDerived.lean:118, commit 37cd21ff; binders: none; from `rootedPhysicalMetricContinuousAtInsertion_of_axioms` :32 with the proved field axioms and LQG metric axioms); docstring verdict was: TRUE | chat 149; notes/fp-gaps/CHATGPT-n2-hecont.md; notes/fp-gaps/CHATGPT-11-15-17-faithful-referee.md | Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.17, printed p. 43 |
| 73 | `LocalMeasureKernelStmt`* | FirstPass/S11r/Frozen.lean:144 | TRUE | chat 148; notes/fp-gaps/CHATGPT-n1-n2-11-13-inputs.md | Bou-Rabee-Gwynne, arXiv:2208.11795v3, Fact 2.1, printed p. 9 |
| 74 | `LocalMarkedRootingIdentityFrozen` | FirstPass/S11r/FrozenMetricReplacement.lean:38 | RETIRED (truth: FALSE AS TYPED) → superseded by LocalMarkedRootingIdentityWeightedFrozen | ChatGPT 01:48 UTC | Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Proposition 1.1, printed p. 184 |
| 75 | `LocalMarkedRootingIdentityWeightedFrozen` | FirstPass/S11r/FrozenMetricReplacement.lean:72 | TRUE | notes/fp-gaps/CHATGPT-n2-frozen-corrected.md | Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma 11.13, printed p. 184 |
| 76 | `LocalMetricReplacementStmt`* | FirstPass/S11r/LocalMetricReplacement.lean:58 | other: "EXTERNAL (see the module docstring," | - | none |
| 77 | `PointwiseBirkhoff` | Proposed/Birkhoff.lean:18 | other: "Birkhoff's pointwise ergodic theorem for" | - | none |
| 78 | `dmsShift` | Proposed/DuplantierMillerSheffield.lean:34 | other: "The function f_z(w) = -γ" | - | none |
| 79 | `dmsConstant` | Proposed/DuplantierMillerSheffield.lean:39 | other: "The additive constant κ =" | - | none |
| 80 | `dmsShiftedPairing` | Proposed/DuplantierMillerSheffield.lean:44 | other: "The raw pairing functional of" | - | none |
| 81 | `DMSLemmaA10WholePlane` | Proposed/DuplantierMillerSheffield.lean:61 | RETIRED → not derived; counted chain uses DMSLemmaA10WholePlaneUnnormalized and DMSLemmaA10WholePlaneMarked | chat 219; notes/fp-gaps/CHATGPT-219-hb-8-2-R9-hL1-hWeyl-PRO.md | arXiv:1409.7055v4, p. 184 |
| 82 | `DMSLemmaA10WholePlaneUnnormalized` | Proposed/DuplantierMillerSheffield.lean:80 | other: "Duplantier-Miller-Sheffield, Lemma A.10, whole-plane clause," | - | arXiv:1409.7055v4, p. 184 |
| 83 | `ExteriorSphereAt` | Proposed/GilbargTrudinger.lean:23 | other: "The exterior sphere condition at" | - | none |
| 84 | `GilbargTrudingerThm2_14` | Proposed/GilbargTrudinger.lean:30 | other: "Gilbarg-Trudinger, Theorem 2.14 (p. 26)," | - | Gilbarg-Trudinger, Theorem 2.14, p. 26 |
| 85 | `WholePlaneGFFAffineInvariance`* | Proposed/LQG.lean:56 | TRUE | Codex truth check 2026-11-1 | arXiv:1910.04713v2, Corollary 5.7, p. 16 |
| 86 | `LQGMeasureExistence`* | Proposed/LQG.lean:74 | TRUE | Codex truth check 2026-11-1 | arXiv:2208.11795v3, Proposition 1.1, p. 9 |
| 87 | `LQGMeasureNonatomic`* | Proposed/LQG.lean:86 | TRUE; DERIVED at every α₀ (2026-11-12): `lqgMeasureNonatomic_holds` and `lqgMeasureNonatomicAll_holds` (FirstPass/Phase2/NonatomicHolds.lean, from Lattice-Probability `LatticeProb.LQG.LQGMeasureNonatomicUpper.lqgMeasureNonatomicLP_holds`, no hypotheses, pin 8275377, std axioms); supplied in the counted form of Phase2/DerivedInputs42.lean (Closure 8.3: hN removed) | Codex truth check 2026-11-1 | arXiv:2404.16642v2, Fact 2.1, p. 9 |
| 88 | `LQGMeasureLocality`* | Proposed/LQG.lean:97 | TRUE | Codex truth check 2026-11-1 | Fact 2.1 |
| 89 | `LQGMeasureWeylScaling`* | Proposed/LQG.lean:107 | other: "Fact 2.1 III (Weyl scaling)" | - | Fact 2.1, p. 9 |
| 90 | `LQGMeasureCoordChange`* | Proposed/LQG.lean:131 | TRUE; DERIVED at every α₀ (2026-11-12): `lqgMeasureCoordChange_holds` and `coordChangeAlpha0Stmt_holds` (FirstPass/Phase2/CoordChangeHolds.lean, from Lattice-Probability `LatticeProb.LQG.coordChangeLP_of_isWholePlaneGFF`, pin e39e841, std axioms; α₀ = 0 earlier: `lqgMeasureCoordChange_zero_holds`, CoordChangeZeroHolds.lean); supplied in the counted forms of Phase2/DerivedInputs40.lean (22) and Phase2/DerivedInputs41.lean (42 forms; new: closure 5.2-5.5, 5.7, 7.2, 8.1, 8.3, 9.2, 10.7, 11.6 and 8.2 S8d drop hCC) | Codex truth check 2026-11-1 | Duplantier-Sheffield, arXiv:1605.06171v2, Fact 2.1, p. 13 |
| 91 | `WholePlaneLQGBallMassBounds`* | Proposed/LQG.lean:172 | TRUE; DERIVED for every γ and every model (2026-11-12): `wholePlaneLQGBallMassBounds_holds` (FirstPass/Phase2/BallMassBoundsHolds.lean, from Lattice-Probability `LatticeProb.LQG.wholePlaneLQGBallMassBoundsLP_holds` through `wholePlaneLQGBallMassBounds_forall_of_LP`); supplied in the counted forms by FirstPass/Phase2/DerivedInputs43.lean (53 forms, 42 without hypotheses; checks/AxiomsDerivedInputs43.lean: standard axioms) | Codex truth check 2026-11-1 | arXiv:1807.01072, Lemma 3.8, p. 25 |
| 92 | `LQGMetricExistenceUniqueness` | Proposed/LQG.lean:196 | TRUE; DERIVED (2026-11-12): `lqgMetricExistenceUniqueness_derived` (Proofs/GFF/LQGMetricUniquenessDerived.lean; binders: none; from Lattice-Probability `theorem11_proved`/`theorem12_proved` via Proofs/GFF/LQGMetricExistence.lean and Proofs/GFF/LQGMetricUniqueness.lean, and `LatticeProb.ae_eq_comp_of_ae_eq_generators`) | Codex truth check 2026-11-1 | Gwynne-Miller, arXiv:1905.00383, Theorem 1.2, p. 6 |
| 93 | `LQGMetricFieldAxioms` | Proposed/LQG.lean:225 | TRUE | Codex truth check 2026-11-1 | Gwynne-Miller, arXiv:1905.00380, Fact 2.2, p. 6 |
| 94 | `WholePlaneLQGGraphDimension`* | Proposed/LQGDimension.lean:19 | other: "LQG graph-distance exponent. Ding--Gwynne, The" | - | arXiv:1807.01072v3, Theorem 1.4, p. 6 |
| 95 | `WholePlaneLQGMetricBoundedlyCompact` | Proposed/MetricProperness.lean:26 | other: "Whole-plane LQG metric bounded compactness." | - | Lemma 3.8, p. 408 |
| 96 | `MillerSheffieldIG4Prop29` | Proposed/MillerSheffieldIG4.lean:48 | other: "Miller-Sheffield, Imaginary Geometry IV, Proposition" | - | arXiv:1302.4738v2, Proposition 2.9, p. 49 |
| 97 | `pfefferCircleAverage` | Proposed/PfefferMetricScaling.lean:46 | other: "The circle average (2π)⁻¹ ∫₀^{2π}" | - | p. 5 |
| 98 | `pfefferAcross` | Proposed/PfefferMetricScaling.lean:51 | other: "The D-distance across the annulus" | - | p. 5 |
| 99 | `PfefferSeparates` | Proposed/PfefferMetricScaling.lean:56 | other: "The closed path P separates" | - | p. 5 |
| 100 | `pfefferAround` | Proposed/PfefferMetricScaling.lean:61 | other: "The D-distance around the annulus" | - | p. 5 |
| 101 | `PfefferIsLengthSpace` | Proposed/PfefferMetricScaling.lean:66 | other: "Axiom I of Definition 1.6" | - | Definition 1.6, p. 5 |
| 102 | `PfefferIsLscMetric` | Proposed/PfefferMetricScaling.lean:71 | other: "A lower semicontinuous metric on" | - | Definition 1.6, p. 6 |
| 103 | `pfefferField` | Proposed/PfefferMetricScaling.lean:76 | other: "The pairing functional h =" | - | none |
| 104 | `pfefferNormalization` | Proposed/PfefferMetricScaling.lean:80 | other: "The normalizing factor c_r⁻¹ e^{-ξ" | - | none |
| 105 | `PfefferTightAcrossScales` | Proposed/PfefferMetricScaling.lean:87 | other: "Tightness over scales, in the" | - | p. 6 |
| 106 | `PfefferAxiomVScale` | Proposed/PfefferMetricScaling.lean:98 | other: "Axiom V of Definition 1.6" | - | Definition 1.6, p. 6 |
| 107 | `PfefferWeakAxioms` | Proposed/PfefferMetricScaling.lean:112 | other: "Axioms I–V of Definition 1.6" | - | Definition 1.6, p. 6 |
| 108 | `IsPfefferWeakLQGMetric` | Proposed/PfefferMetricScaling.lean:135 | other: "A weak LQG metric with" | - | Definition 1.6, p. 6 |
| 109 | `PfefferBackgroundScaling` | Proposed/PfefferMetricScaling.lean:146 | other: "Proposition 1.9, equation (1.10) (p." | - | Proposition 1.9, p. 8 |

## 4. Hand checks

Mechanical checks (scratch-z6/gen_status.py and a verification pass, both uncommitted): all evidence references and all 42 quoted verdict phrases occur verbatim in their docstrings; the literature locators were checked part by part (author, arXiv id, theorem, page) against the docstring text, 0 mismatches; every TRUE or FALSE status has its verdict word in the docstring. Limits: a locator part is the first match in the docstring, so a theorem number may be the paper's own (e.g. `Lemma 11.7`) rather than the literature's; quotes are copied, not interpreted.

Hand checks against the source, 8 rows:
1. `CameronMartinGFFReweighting` (FirstPass/Frozen/S11aj.lean:33): DERIVED INTERFACE, truth TRUE, chat 179 and chat 151; locator Miller-Sheffield, arXiv:1302.4738v2, Proposition 2.9, printed p. 49. As written.
2. `LocalLQGInsertionWeylOffOrigin` (FirstPass/Frozen/S8c.lean:85): RETIRED, truth TRUE, target `localLQGInsertionWeylOffOrigin_derived` at FirstPass/S8c/WeylOffOriginDerived.lean:88 (line confirmed by grep).
3. `DMSLemmaA10WholePlaneMarkedSub` (FirstPass/Frozen/S11i.lean:58): TRUE (operator ruling 2026-11-10; chat 241, notes/fp-gaps/CHATGPT-241-hb-DMS-A10-marked-truth-PRO.md §4). The docstring states "Truth check: TRUE" for the Sub form, which inserts `0 < γ`, `γ < 2` into the statement. The FALSE verdict of that note applies to the unrestricted `DMSLemmaA10WholePlaneMarked` only (FirstPass/Frozen/S11i.lean, old def, unchanged).
4. `WholePlaneGFFExistsFrozen` (FirstPass/S11r/Frozen.lean:39): TRUE, ChatGPT 01:17 UTC, notes/fp-gaps path. As written.
5. `LQGMeasureExistence` (Proposed/LQG.lean:74): TRUE; Codex truth check 2026-11-1x; locator arXiv:2208.11795v3, Proposition 1.1, p. 9. As written.
6. `PfefferBackgroundScaling` (Proposed/PfefferMetricScaling.lean:146): other, no verdict word; quote and locator (Proposition 1.9, p. 8) as written.
7. `LocalMetricReplacementFrozen` (FirstPass/Frozen/S11rMetric.lean:33): other, quote "Truth: no counterexample, quantifier structure", Codex Sol 2026-11-10.
8. `CircleAverageVersionMeasurableStmt` (FirstPass/Frozen/S11i.lean:24): RETIRED, derived from `IsWholePlaneGFF.ae_continuousOn_circle`; the docstring names no theorem, so no file:line is given.

Observations for the operator (not judged): `LQGMetricAlphaWeylShiftLengthFrozen` (FirstPass/Frozen/S11m.lean:30) is labelled FIRST-PASS FROZEN but its docstring says "derived: lqgMetricAlphaWeylShiftLength_of_axioms"; no RETIRED label. Two RETIRED or FALSE rows name no replacement (`LQGInternalMetricContinuousFrozen`, `LQGMetricLengthIdentityFrozen`). `DMSLemmaA10WholePlaneMarkedSub` is TRUE (observation 4), not RETIRED or FALSE.
