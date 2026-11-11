import HarmonicBalls.FirstPass.S11m.Final11_12
import HarmonicBalls.FirstPass.S11i.Corrected11_13
import HarmonicBalls.FirstPass.Closure.Sec11

/-!
# Axiom and hypothesis check: 11.12, 11.13 and the closures of Section 11
No statement or proof is changed by this file.

Part 1: `#print axioms` for `firstPass_11_12_final`, `firstPass_11_13_corrected` and the fourteen `closure_11_*`
of `FirstPass/Closure/Sec11.lean`. Expected output: only `propext`, `Classical.choice`, `Quot.sound`.

Part 2: the hypotheses of `HarmonicBalls.S11m.Final11_12.firstPass_11_12_final` (`S11m/Final11_12.lean:131-158`), with the
location of the Prop and the status its docstring gives. Paths relative to `HarmonicBalls/`.

| # | binder | Prop (file:line) | status in the docstring |
|---|---|---|---|
| 1 | `hAx` | `LQGMetricFieldAxiomsUnivFrozen` (`FirstPass/Frozen/S11j.lean:143`) | FROZEN; truth check TRUE; also "pending operator source-check" |
| 2 | `hLen` | `LQGMetricLengthUnivFrozen` (`FirstPass/Frozen/S11j.lean:133`) | FROZEN, EXTERNAL; truth check TRUE; source Gwynne-Miller Thm 1.2, Fact 2.2 I |
| 3 | `hN2` | `LocalMetricReplacementStmt` (`FirstPass/S11r/LocalMetricReplacement.lean:53`) | FROZEN, EXTERNAL; truth TRUE in substance; sources Gwynne-Miller Axiom II, Thm 1.2, Rem 1.5; DFGPS Thm 1.10, Prop 3.17 |
| 4 | `hμW` | `LQGMeasureWeylScaling` (`Proposed/LQG.lean:95`) | Proposed; source paper Fact 2.1 III (line 406, 418); no truth check |
| 5 | `hLoc` | `LocalLQGDecoderCommonFrozen` (`FirstPass/Frozen/S11c.lean:386`) | FROZEN; truth-checked TRUE; source Duplantier-Sheffield Prop 1.1, 3.1 |
| 6 | `hCanon` | `LQGCanonicalDecodersExistStmt` (`FirstPass/Frozen/S11n.lean:30`) | FROZEN, EXTERNAL; truth TRUE; sources DS, Gwynne-Miller Thm 1.2, DFGPS |
| 7 | `hNonat` | `LQGMeasureNonatomicAll` (`FirstPass/S11n/MeasureDecoder.lean:34`) | Proposed (universal form of `LQGMeasureNonatomic`, `Proposed/LQG.lean:77`); source Fact 2.1 I (`paper/lqg_harmonic_ball-corrected.tex:408`); truth TRUE as quantified; operator source-check not yet recorded |
| 8 | `hExists` | `WholePlaneGFFExistsFrozen` (`FirstPass/S11r/Frozen.lean:37`) | FROZEN; truth TRUE; sources Miller-Sheffield IG IV sec. 2.2.1, DS |
| 9 | `hDG` | `WholePlaneLQGBallMassBounds` (`Proposed/LQG.lean:154`) | Proposed; source Ding-Gwynne Lemma 3.8 (quoted); no truth check |
| 10 | `hCC` | `LQGMeasureCoordChange` (`Proposed/LQG.lean:116`) | Proposed; source paper Fact 2.1 IV (line 412), DS 2011 Prop 2.1, Sheffield-Wang Thms 1.1, 1.4 |
| 11 | `hE` | `LQGMeasureExistence` (`Proposed/LQG.lean:68`) | Proposed; source Bou-Rabee-Gwynne sec. 2.2 p. 9, DS Prop 1.1, Berestycki-Powell Thm 2.1 |
| 12 | `hfr` | `LQGInternalMetricWeylAeMeasurableFrozen` (`FirstPass/Frozen/S11d.lean:123`) | FROZEN; truth TRUE; locator pending |
| 13 | `hmass` | `LQGMassFunctionalMeasurableFrozen` (`FirstPass/Frozen/S11d.lean:144`) | FROZEN; truth TRUE; source DS 2011 sec. 3, Fact 2.1 III |
| 14 | `hCMAbs` | `CameronMartinGFFMutualAbsCont` (`FirstPass/Frozen/S11d.lean:74`) | FROZEN; locator MS IG IV Prop 2.9; UNCLEAR for the unrestricted σ-algebra; TRUE for the restated version |
| 15 | `hCMRew` | `CameronMartinGFFReweighting` (`FirstPass/Frozen/S11aj.lean:31`) | FROZEN; truth TRUE as typed; source Miller-Sheffield IG IV Prop 2.9 (p. 49) |
| 16 | `hComp` | `WeylScalingCompositionFrozen` (`FirstPass/Frozen/S11d.lean:89`) | FROZEN; truth TRUE; source paper Fact 2.2 III (line 445), Gwynne-Miller, DFGPS |
| 17 | `hDsm` | `SmallMetricDiameterLargeMassStmt` (`Draft/Section11.lean:201`) | Draft: Proposition 11.9 (paper line 2959) |
| 18 | `hMf` | `LQGMassInnerMeasurableFrozen` (`FirstPass/Frozen/S11k.lean:58`) | FROZEN; truth TRUE; source BRG Fact 2.1 II p. 9; locator pending |
| 19 | `hDiam` | `LQGInternalDiamInnerMeasurableFrozen` (`FirstPass/Frozen/S11k.lean:74`) | FROZEN; truth TRUE; sources BRG Fact 2.2 II, Gwynne-Miller Axiom II |
| 20 | `hMk` | `DomainMarkovConditionalPositiveFrozen` (`FirstPass/Frozen/S11k.lean:43`) | FROZEN; truth TRUE; sources MS IG IV Props 2.8, 2.9; locator pending |
| 21 | `hholder` | `GreenPotentialHolderStmt` (`Draft/Section2.lean:190`) | Draft: Proposition 2.5 Green-potential clause (paper line 524) |

Flags after the docstring round: none open for #3, #7, #12, #14. Their docstrings now carry a
verdict and a source (`S11n/MeasureDecoder.lean`, `Frozen/S11d.lean`). Still open: #1 (`hAx`) has only a truth-check verdict
and a "pending operator source-check" note. Proposed #4, #9, #10, #11 cite sources but carry no truth-check verdict (accepted under the rule above).
Under the classification of the task, a hypothesis is acceptable if it is FROZEN with a truth check, Proposed with a source,
or a Draft numbered result.
-/
