import HarmonicBalls.FirstPass.S11m.Final11_12
import HarmonicBalls.FirstPass.S11i.Corrected11_13
import HarmonicBalls.FirstPass.Closure.Sec11

/-!
# Axiom and hypothesis audit: first-pass 11.12, 11.13 and the closures of Section 11
(fp-S11at-11-12-11-13-axioms-audit, owner q3). No statement or proof is changed by this file.

Part 1: `#print axioms` for `firstPass_11_12_final`, `firstPass_11_13_corrected` and the fourteen `closure_11_*`
of `FirstPass/Closure/Sec11.lean`. Expected output: only `propext`, `Classical.choice`, `Quot.sound`.

Part 2: the hypotheses of `HarmonicBalls.S11m.Final11_12.firstPass_11_12_final` (`S11m/Final11_12.lean:131-150`), with the
location of the Prop and the status its docstring gives. Paths relative to `HarmonicBalls/`.

| # | binder | Prop (file:line) | status in the docstring |
|---|---|---|---|
| 1 | `hAx` | `LQGMetricFieldAxiomsUnivFrozen` (`FirstPass/Frozen/S11j.lean:143`) | FROZEN; truth check TRUE (ChatGPT, 00:28 UTC); also "pending operator source-check" |
| 2 | `hLen` | `LQGMetricLengthUnivFrozen` (`FirstPass/Frozen/S11j.lean:133`) | FROZEN, EXTERNAL; truth check TRUE; source Gwynne-Miller Thm 1.2, Fact 2.2 I |
| 3 | `hN2` | `LocalMetricReplacementStmt` (`FirstPass/S11r/LocalMetricReplacement.lean:53`) | NO label; target statement, sourced to a ChatGPT note (`CHATGPT-n3-B1-B2.md` section 4); NO truth-check verdict. FLAG |
| 4 | `hμW` | `LQGMeasureWeylScaling` (`Proposed/LQG.lean:95`) | Proposed; source paper Fact 2.1 III (line 406, 418); no truth check |
| 5 | `hLoc` | `LocalLQGDecoderCommonFrozen` (`FirstPass/Frozen/S11c.lean:386`) | FROZEN; truth-checked TRUE (ChatGPT 2026-11-09); source Duplantier-Sheffield Prop 1.1, 3.1 |
| 6 | `hCanon` | `LQGCanonicalDecodersExistStmt` (`FirstPass/Frozen/S11n.lean:30`) | FROZEN, EXTERNAL; truth TRUE (ChatGPT 23:53 UTC); sources DS, Gwynne-Miller Thm 1.2, DFGPS |
| 7 | `hNonat` | `LQGMeasureNonatomicAll` (`FirstPass/S11n/MeasureDecoder.lean:34`) | Proposed (universal form of `LQGMeasureNonatomic`, `Proposed/LQG.lean:75`); "pending operator source-check"; NO source, NO truth check. FLAG |
| 8 | `hExists` | `WholePlaneGFFExistsFrozen` (`FirstPass/S11r/Frozen.lean:37`) | FROZEN; truth TRUE (ChatGPT 01:17 UTC); sources Miller-Sheffield IG IV sec. 2.2.1, DS |
| 9 | `hDG` | `WholePlaneLQGBallMassBounds` (`Proposed/LQG.lean:154`) | Proposed; source Ding-Gwynne Lemma 3.8 (quoted); no truth check |
| 10 | `hCC` | `LQGMeasureCoordChange` (`Proposed/LQG.lean:116`) | Proposed; source paper Fact 2.1 IV (line 412), DS 2011 Prop 2.1, Sheffield-Wang Thms 1.1, 1.4 |
| 11 | `hE` | `LQGMeasureExistence` (`Proposed/LQG.lean:68`) | Proposed; source Bou-Rabee-Gwynne sec. 2.2 p. 9, DS Prop 1.1, Berestycki-Powell Thm 2.1 |
| 12 | `hfr` | `LQGInternalMetricWeylAeMeasurableFrozen` (`FirstPass/Frozen/S11d.lean:123`) | FROZEN; "standard; locator pending"; refers to a truth check "of 19:20 UTC" without stating its verdict. FLAG |
| 13 | `hmass` | `LQGMassFunctionalMeasurableFrozen` (`FirstPass/Frozen/S11d.lean:144`) | FROZEN; truth TRUE (ChatGPT 02:36 UTC); source DS 2011 sec. 3, Fact 2.1 III |
| 14 | `hCMAbs` | `CameronMartinGFFMutualAbsCont` (`FirstPass/Frozen/S11d.lean:74`) | FROZEN; "standard; locator MS IG IV Prop 2.9"; refers to a truth check "19:20 UTC" without stating its verdict. FLAG |
| 15 | `hCMRew` | `CameronMartinGFFReweighting` (`FirstPass/Frozen/S11aj.lean:31`) | FROZEN; truth TRUE as typed; source Miller-Sheffield IG IV Prop 2.9 (p. 49) |
| 16 | `hComp` | `WeylScalingCompositionFrozen` (`FirstPass/Frozen/S11d.lean:89`) | FROZEN; truth TRUE (ChatGPT batch 02:49 UTC); source paper Fact 2.2 III (line 445), Gwynne-Miller, DFGPS |
| 17 | `hDsm` | `SmallMetricDiameterLargeMassStmt` (`Draft/Section11.lean:201`) | Draft: Proposition 11.9 (paper line 2959) |
| 18 | `hMf` | `LQGMassInnerMeasurableFrozen` (`FirstPass/Frozen/S11k.lean:58`) | FROZEN; truth TRUE (ChatGPT, operator note 23:27 UTC); source BRG Fact 2.1 II p. 9; locator pending |
| 19 | `hDiam` | `LQGInternalDiamInnerMeasurableFrozen` (`FirstPass/Frozen/S11k.lean:74`) | FROZEN; truth TRUE (ChatGPT, operator note 23:27 UTC); sources BRG Fact 2.2 II, Gwynne-Miller Axiom II |
| 20 | `hMk` | `DomainMarkovConditionalPositiveFrozen` (`FirstPass/Frozen/S11k.lean:43`) | FROZEN; truth TRUE (ChatGPT, operator note 23:27 UTC, sec. 4.1); sources MS IG IV Props 2.8, 2.9; locator pending |
| 21 | `hholder` | `GreenPotentialHolderStmt` (`Draft/Section2.lean:190`) | Draft: Proposition 2.5 Green-potential clause (paper line 524) |

Flags: #3 and #7 have no truth-check verdict; #7 has no source. #12 and #14 name a truth check but do not state its verdict.
Under the classification of the task, a hypothesis is acceptable if it is FROZEN with a truth check, Proposed with a source,
or a Draft numbered result.
-/

#print axioms HarmonicBalls.S11m.Final11_12.firstPass_11_12_final
#print axioms HarmonicBalls.firstPass_11_13_corrected
#print axioms HarmonicBalls.Closure.closure_11_2
#print axioms HarmonicBalls.Closure.closure_11_5
#print axioms HarmonicBalls.Closure.closure_11_6
#print axioms HarmonicBalls.Closure.closure_11_7
#print axioms HarmonicBalls.Closure.closure_11_8
#print axioms HarmonicBalls.Closure.closure_11_9
#print axioms HarmonicBalls.Closure.closure_11_10
#print axioms HarmonicBalls.Closure.closure_11_11
#print axioms HarmonicBalls.Closure.closure_11_12
#print axioms HarmonicBalls.Closure.closure_11_13
#print axioms HarmonicBalls.Closure.closure_11_14
#print axioms HarmonicBalls.Closure.closure_11_15
#print axioms HarmonicBalls.Closure.closure_11_16
#print axioms HarmonicBalls.Closure.closure_11_17
