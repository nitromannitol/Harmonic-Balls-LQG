import HarmonicBalls.FirstPass.Main
import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.FirstPass.Closure.Sec6
import HarmonicBalls.FirstPass.Closure.SecA45
import HarmonicBalls.FirstPass.Closure.Sec78910
import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.Closure.Bridge12

/-!
# Closure aggregator for the counted numbered results of "Harmonic balls in Liouville quantum gravity"

Owner: z3 (task fp-closure-main-aggregator-3). File `HarmonicBalls/FirstPass/Closure.lean`, namespace `HarmonicBalls.Closure`.

Convention. For a counted numbered result `X.Y`, `closure_X_Y` has the conclusion of the counted first-pass theorem
`firstPass_X_Y` (`FirstPass/*.lean`). Its hypotheses are FIRST-PASS FROZEN Props (`FirstPass/Frozen/*.lean`), PROPOSED
Props (`Proposed/LQG.lean`, pending operator source-check), or CITED Props (operator ruling 04:40 UTC, `tasks/lh.md`).
Every paper-owned hypothesis is discharged by the closure of its result, recursively. The closures of this file and of
`Closure/*.lean` are applications only. OPEN means: no proof in the repository, listed as a hypothesis where a closure
exists at all.

## Table (every counted result; closure name; remaining hypotheses and class; status)

Section 1 (main theorems; `FirstPass/Main.lean`)
| result | closure | remaining hypotheses (class) | status |
|---|---|---|---|
| 1.1 `ExistenceUniquenessHarmonicBallsStmt` | `closure_1_1` (this file) | hL1 hWeyl hE1 hE3 hB (FROZEN); hDG hAff hCC hW hE hN (PROPOSED) | closed |
| 1.2 `HarmonicBallNoveltyStmt` | `closure_1_2` (this file) | h13 = `manyPinchScales_of_corrected (closure_11_13 …)` (bridge, `Closure/Bridge12.lean`, z7, committed 96e95db); hStep8 `Step8IdentificationStmt` **OPEN** (inherited from `closure_11_13`); hI2 (Input I2, EXTERNAL per `FIRST-PASS-INPUTS.md`); hDG hAff hCC hW hE hN (PROPOSED); hL1 hWeyl hE1 hE3 hB, hCamp hDecFrozen hDec hCM, hAx `LQGMetricFieldAxiomsUnivFrozen` (FROZEN; supplies hmetricAxioms by specialisation), hTor (FROZEN) | conditional on OPEN hStep8 |
| 1.3 `HarmonicBallLocalSetStmt` | `closure_1_3` (this file) | hI2 = I2 `LQGVolumeGrowthAllScalesStmt` (`Draft/Section2.lean:122`; class EXTERNAL per `FIRST-PASS-INPUTS.md`; explicit argument here; discharged from hDG hCC hW hE hN by `volumeGrowthI2_of_staged`, `Closure/Sec11.lean:55`, not passed); hmeasure `LQGMeasureLocality` (PROPOSED); closure_8_2 inputs (FROZEN, PROPOSED) | closed modulo the I2 argument |

Section 2
| 2.3 `GreenFunctionBallStmt` | `closure_2_3` (this file) | none (unconditional `firstPass_2_3`) | closed |
| 2.5 `GreenPotentialLiouvilleHolderStmt` | none | CITED: `GreenPotentialHolderStmt` (`Draft/Section2.lean:190`) is the cited input hholder (operator 04:40 UTC); no closure | CITED |
| 2.1, 2.2, 2.4, 2.6 | none | cited results (not paper-owned) | cited, no closure |

Section 3 (`FirstPass/S2S3S4S9SA.lean`; this file)
| 3.1 `LeastSupersolutionMemStmt` | `closure_3_1` | hDG hAff hCC hW hE hN (PROPOSED) | closed |
| 3.2 `ClusterOpenLaplacianStmt` | `closure_3_2` | hDG hAff hCC hW hE hN (PROPOSED) | closed |
| 3.3 `ClusterMonotoneStmt` | `closure_3_3` | hDG hAff hCC hW hE hN (PROPOSED) | closed |
| 3.4 `ClusterConservationOfMassStmt` | `closure_3_4` | hDG hAff hCC hW hE hN (PROPOSED) | closed |
| 3.5 `ClusterCompatibilityStmt` | `closure_3_5` | hDG hAff hCC hW hE hN (PROPOSED) | closed |

Section 4 and Appendix A (`Closure/SecA45.lean`, z6, commit 0ff1bdd)
| 4.1 `ClusterLowerBoundStmt` | `closure_4_1` | hDG hCC hW hE hN (PROPOSED) | closed |
| 4.2 `LeastSupersolutionHolderStmt` | `closure_4_2` | hDG hCC hW hE hN (PROPOSED) | closed |
| 4.3 `ClusterSubharmonicBallStmt` | `closure_4_3` | hDG hCC hW hE hN (PROPOSED) | closed |
| A.1-A.6 | `closure_A_1`..`closure_A_6` | none | closed |

Section 5 (`Closure/SecA45.lean`, z6)
| 5.1 `ClusterUpperBoundStmt` | `closure_5_1` | hDG hCC hE (PROPOSED) | closed |
| 5.2 `ClusterContinuityStmt` | `closure_5_2` | hDG hCC hE hW hN (PROPOSED); hL1 hWeyl hE1 hE3 hB (FROZEN) | closed |
| 5.3 `ClusterBoundaryMeasureZeroStmt` | `closure_5_3` | as 5.2 | closed |
| 5.4 `RegularizedClusterHarmonicBallsStmt` | `closure_5_4` | as 5.2 | closed |
| 5.5 `ExistenceHarmonicBallsStmt` | `closure_5_5` | as 5.2 | closed |
| 5.6 `UniquenessHarmonicBallsStmt` | `closure_5_6` | hDG hCC hE (PROPOSED) | closed |
| 5.7 `ClusterScaleInvarianceStmt` | `closure_5_7` | hDG hCC hE (PROPOSED) | closed |
| 5.8 `ClusterStrongCompatibilityStmt` | `closure_5_8` | hDG hCC hE (PROPOSED) | closed |

Section 6 (`Closure/Sec6.lean`, z3, commit 324b59b)
| 6.1, 6.2, 6.3, 6.4, 6.6-6.13 | `closure_6_1`, `closure_6_2`, `closure_6_3`, `closure_6_4`, `closure_6_6`..`closure_6_13` | hDG hCC hE (PROPOSED) | closed |
| 6.5 | none | cited (Gwynne-Miller 2020, Lemma 3.1); not paper-owned | cited, no closure |

Sections 7-10 (`Closure/Sec78910.lean`, z7, commit 764a353)
| 7.1 `ClusterUpperBoundPolyHighProbStmt` | `closure_7_1` | hDG hCC hE (PROPOSED) | closed |
| 7.2 `ClusterTimeContinuityStmt` | `closure_7_2` | hL1 hWeyl hE1 hE3 hB (FROZEN); hDG hAff hCC hW hE hN (PROPOSED) | closed |
| 8.1 `BoundaryMeasureZeroOfCompactClusterStmt` | `closure_8_1` | as 7.2 | closed |
| 8.2 `TypicalPointManyGoodScalesStmt` | `closure_8_2` | as 7.2 | closed |
| 8.3 `OriginManyGoodScalesStmt` | `closure_8_3` | hholder CITED (Prop 2.5); hDG hCC hE hW hN (PROPOSED) | closed, cited input |
| 9.2 `SubharmonicBallUniquenessStmt` | `closure_9_2` | as 7.2 | closed |
| 9.3 `HarmonicBallBoundarySubsetStmt` | `closure_9_3` | hDG hAff hCC hW hE hN (PROPOSED) | closed |
| 9.4 `RegularOpenEqOfAEEqStmt` | `closure_9_4` | hDG hAff hCC hW hE hN (PROPOSED) | closed |
| 10.1 `ClusterBoundedCrossingsStmt` | `closure_10_1` | hDG hCC hW hE hN (PROPOSED) | closed |
| 10.5 `CrossingComponentContainsClusterCrossingStmt` | `closure_10_5` | premises on G (`hGne`, `hGb`, `hGo`, `hGc`: nonempty, bounded, open, connected) and `hEcross` (quantifiers of the counted theorem, not Props); hTor (FROZEN) | closed |
| 10.6 `ComplementComponentBoundarySimpleLoopStmt` | `closure_10_6` | hDG hAff hCC hW hE hN (PROPOSED); hTor (FROZEN) | closed |
| 10.7 `HarmonicBallComplementBoundaryJordanStmt` | `closure_10_7` | hL1 hWeyl hE1 hE3 hB hTor (FROZEN); hDG hAff hCC hW hE hN (PROPOSED) | closed |
| 9.1 | none | cited (Shahgholian-Sjodin 2013; Sakai 1984) | cited, no closure |

Section 11 (`Closure/Sec11.lean`, z11; last commit afa5737)
| 11.2 `HarmonicBallNotLipschitzStmt` | `closure_11_2` | hDG hCC hE hW hN (PROPOSED); hL1 hWeyl hE1 hE3 hB (FROZEN); hCamp hDecFrozen hDec hCM (FROZEN); I2 discharged in the proof | closed |
| 11.5 `NoConeConditionStmt` | `closure_11_5` | as 11.2 | closed |
| 11.6 `AnnulusMassBoundByHarmonicChainStmt` | `closure_11_6` | hDG hCC hE hW hN (PROPOSED); hL1 hWeyl hE1 hE3 hB (FROZEN); I2 discharged in the proof | closed |
| 11.7 `ManyConeBadScalesStmt` | `closure_11_7` | hDG hCC hE hNA (PROPOSED); hCamp hDecFrozen hDec hCM (FROZEN) | closed |
| 11.8 `ConeBadEventProbabilityStmt` | `closure_11_8` | hDG hCC hE (PROPOSED) | closed |
| 11.10 `SmallMetricDiameterLargeMassSquareStmt` | `closure_11_10` | FROZEN and PROPOSED (hAx, hShift; detail in `Closure/Sec11.lean`) | closed |
| 11.11 `HarmonicBallNotMetricBallStmt` | `closure_11_11` | hDG hCC hE hW hN (PROPOSED); hL1 hWeyl hE1 hE3 hB (FROZEN); hAx `LQGMetricFieldAxiomsUnivFrozen` (FROZEN); hStep8 `Step8IdentificationStmt` **OPEN** (inherited from `closure_11_13`); the printed Lemma 11.13 is discharged inside by `manyPinchScales_of_corrected`; I2 discharged inside (`volumeGrowthI2_of_staged`) | conditional on OPEN hStep8 |
| 11.13 `CorrectedLemma11_13Stmt` | `closure_11_13` | hAx, hE (FROZEN, PROPOSED); hStep8 `Step8IdentificationStmt` **OPEN** (`FirstPass/S11i/Corrected11_13.lean:57`) | conditional on OPEN hStep8 |
| 11.14 `PinchEventMetricBallConsequenceStmt` | `closure_11_14` | hAx (FROZEN) | closed |
| 11.15 `PinchFirstEventFaithfulStmt` | `closure_11_15` | hCM hMet hWSC hAx hExists (FROZEN) | closed |
| 11.9 `SmallMetricDiameterLargeMassStmt` | `closure_11_9` | FROZEN, PROPOSED and CITED inputs of 11.9 and 11.10 (table in `Closure/Sec11.lean`) | closed |
| 11.12 `CorrectedLemma11_12Stmt` | `closure_11_12` | z4 inputs (`hLen`, `hμW`, `hLoc`, `hCanon`, `hNonat`, `hExists`, `hfr`, `hmass`, `hCMAbs`, `hCMRew`, `hComp`, `hMf`, `hDiam`, `hMk`, `hholder`, `hShift`, `hFD`, `hDC`, `hCMT`, `hPos10`, `hMassM`, `hSupM`, `hFin`, `hW`, `hM1`, `hM2`, `hDG`, `hCC`, `hE`, `hAx`); hN2 (FROZEN, kept per operator 04:48); I2 derived inside the proof (`S11m/Final11_12.lean`; no `hgrowth` argument) | closed (`#print axioms`: propext, Classical.choice, Quot.sound) |
| 11.16 `PinchSecondEventFaithfulStmt` | `closure_11_16` | closures 11.15 and 11.9; hholder (CITED, Prop 2.5); FROZEN; PROPOSED hEx hWeyl hNa0 hNa | closed |
| 11.17 `PinchThirdEventFaithfulStmt` | `closure_11_17` | closure 11.16; hN2 (FROZEN) | closed |

## Open items and flags
* 1.2 is closed modulo the OPEN `hStep8` of `closure_11_13` (table above). The printed Lemma 11.13 is supplied by the bridge
  `manyPinchScales_of_corrected` (`Closure/Bridge12.lean`, committed 96e95db); no ManyPinchScalesStmt hypothesis remains.
* I2 `LQGVolumeGrowthAllScalesStmt` is an explicit argument of `closure_1_2` and `closure_1_3` only. Closures 11.2, 11.5,
  11.6 and 11.11 discharge it by `volumeGrowthI2_of_staged` (`Closure/Sec11.lean:55`); 11.12 derives it inside its proof
  (`FirstPass/S11m/Final11_12.lean`). Not OPEN in the sense of this file: a proof exists from the same PROPOSED inputs; its
  classification is the operator's (`docs/campaign/CORRECTIONS.md:60-62`).
* Sec11 is committed in full (afa5737, 14 closures); this file builds against that version.
* Commit 85bdd95 (z11) overwrote this file with a Section 1 version whose `closure_1_2` takes `ManyPinchScalesStmt` as an OPEN hypothesis. This version restores the table above; `closure_1_2` here takes no ManyPinchScalesStmt hypothesis.

Cycles: none found. Closures used by this file do not refer back to Section 1.
-/

namespace HarmonicBalls.Closure

universe u

/-- Closure of Proposition 2.3 (`prop:green-properties`): the Green function of a ball. Unconditional. -/
theorem closure_2_3 : GreenFunctionBallStmt := firstPass_2_3

section LiteratureInputs

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
  (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)

include hDG hAff hCC hW hE hN

/-- Closure of Lemma 3.1 (`lemma:basic-properties`): least supersolution membership. -/
theorem closure_3_1 : LeastSupersolutionMemStmt.{u} := firstPass_3_1 hDG hAff hCC hW hE hN

/-- Closure of Lemma 3.2 (`lemma:non-coincidence-open-harmonic`): the cluster is an open Laplacian set. -/
theorem closure_3_2 : ClusterOpenLaplacianStmt.{u} := firstPass_3_2 hDG hAff hCC hW hE hN

/-- Closure of Lemma 3.3: monotonicity of the cluster in the scale. -/
theorem closure_3_3 : ClusterMonotoneStmt.{u} := firstPass_3_3 hDG hAff hCC hW hE hN

/-- Closure of Lemma 3.4: conservation of mass of the cluster. -/
theorem closure_3_4 : ClusterConservationOfMassStmt.{u} := firstPass_3_4 hDG hAff hCC hW hE hN

/-- Closure of Lemma 3.5 (`lemma:cluster-compatibility`): compatibility of the clusters across scales. -/
theorem closure_3_5 : ClusterCompatibilityStmt.{u} := firstPass_3_5 hDG hAff hCC hW hE hN

end LiteratureInputs

section MainTheorems

/-- Closure of Theorem 1.1 (`theorem:harmonic-balls`): existence and uniqueness of the harmonic balls. Composition
`firstPassMain_1_1` (`FirstPass/Main.lean:33`) with Lemma 8.2 discharged by `closure_8_2` (`Closure/Sec78910.lean`). -/
theorem closure_1_1
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ExistenceUniquenessHarmonicBallsStmt.{u} :=
  firstPassMain_1_1 hDG hCC hE (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN)

/-- **Closure of Theorem 1.2** (`HarmonicBallNoveltyStmt`, `firstPassMain_1_2`, `theorem:harmonic-balls-properties`): novelty
of the harmonic balls, i.e. the Jordan clause (Proposition 10.7), the non-Lipschitz clause (Proposition 11.2) and the
non-metric-ball clause (Proposition 11.11). Discharged: Lemma 8.2 by `closure_8_2`; Lemma 11.7 by `closure_11_7`; the
printed Lemma 11.13 (`ManyPinchScalesStmt`) by the bridge `manyPinchScales_of_corrected` (`Closure/Bridge12.lean`) applied to
`closure_11_13`; `hmetricAxioms` by specialisation of the FROZEN universal form `LQGMetricFieldAxiomsUnivFrozen`
(`Frozen/S11j.lean:143`). Remaining hypotheses: `hStep8` (OPEN, `Step8IdentificationStmt`, inherited from `closure_11_13`),
`hI2` (Input I2, `LQGVolumeGrowthAllScalesStmt`, EXTERNAL per `docs/campaign/FIRST-PASS-INPUTS.md`), and the PROPOSED and
FROZEN inputs listed in the table of this file. -/
theorem closure_1_2
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hStep8 : Step8IdentificationStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPassMain_1_2 hDG hAff hCC hW hE hN hI2
    (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN)
    (closure_11_7 hDG hCamp hDecFrozen hDec hCM
      (fun γ α₀ Ω _ P hC hcirc => hCC Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hE Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hN Ω P γ α₀ hC hcirc))
    (manyPinchScales_of_corrected (closure_11_13 hAx hE hStep8))
    hTor
    (fun γ α₀ ξ _ _ _ Ω _ P hC hcirc _ => hAx Ω P γ ξ α₀ hC hcirc)

/-- Closure of Proposition 1.3 (`prop:locally-determined`): closed harmonic balls are local sets for the field.
Composition `firstPassMain_1_3` (`FirstPass/Main.lean:104`) with Lemma 8.2 discharged by `closure_8_2`. -/
theorem closure_1_3
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    HarmonicBallLocalSetStmt.{u} :=
  firstPassMain_1_3 hI2 hDG hCC hE (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN) hmeasure

end MainTheorems

end HarmonicBalls.Closure
