import HarmonicBalls.FirstPass.Main
import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.FirstPass.Closure.Sec6
import HarmonicBalls.FirstPass.Closure.SecA45
import HarmonicBalls.FirstPass.Closure.Sec78910
import HarmonicBalls.FirstPass.Closure.Sec11

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
| 1.2 `HarmonicBallNoveltyStmt` | not yet in this file (`closure_1_2` drafted and type-checked in scratch with the bridge as a hypothesis; it is added when `Closure/Bridge12.lean` is committed) | h13 `ManyPinchScalesStmt` = `manyPinchScales_of_corrected (closure_11_13 …)` (bridge, z7, uncommitted); hStep8 `Step8IdentificationStmt` **OPEN** (inherited from `closure_11_13`); hI2 (I2, class open); hDG hAff hCC hW hE hN (PROPOSED); hL1 hWeyl hE1 hE3 hB, hCamp hDecFrozen hDec hCM, hAx `LQGMetricFieldAxiomsUnivFrozen` (FROZEN; supplies hmetricAxioms by specialisation), hTor (FROZEN) | waits on bridge z7; conditional on OPEN hStep8 and hI2 |
| 1.3 `HarmonicBallLocalSetStmt` | `closure_1_3` (this file) | hI2 = I2 `LQGVolumeGrowthAllScalesStmt` (`Draft/Section2.lean:122`; class EXTERNAL per `FIRST-PASS-INPUTS.md`; z4 notes: its derivation is unproved); hmeasure `LQGMeasureLocality` (PROPOSED); closure_8_2 inputs (FROZEN, PROPOSED) | closed, I2 class open |

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
| 10.5 `CrossingComponentContainsClusterCrossingStmt` | `closure_10_5` | premises on G (`hGne`, `hGb`) and `hEcross` (quantifiers of the counted theorem, not Props); hTor (FROZEN) | closed |
| 10.6 `ComplementComponentBoundarySimpleLoopStmt` | `closure_10_6` | hDG hAff hCC hW hE hN (PROPOSED); hTor (FROZEN) | closed |
| 10.7 `HarmonicBallComplementBoundaryJordanStmt` | `closure_10_7` | hL1 hWeyl hE1 hE3 hB hTor (FROZEN); hDG hAff hCC hW hE hN (PROPOSED) | closed |
| 9.1 | none | cited (Shahgholian-Sjodin 2013; Sakai 1984) | cited, no closure |

Section 11 (`Closure/Sec11.lean`, z11; committed in 989dd74, 329d919, 39dfaa9, eb693a6)
| 11.2 `HarmonicBallNotLipschitzStmt` | `closure_11_2` | hI2 (EXTERNAL, see 1.3); hAff hDG hCC hE hW hN, hL1 hWeyl hE1 hE3 hB (PROPOSED or FROZEN); hCamp hDecFrozen hDec hCM (FROZEN) | closed, I2 open |
| 11.5 `NoConeConditionStmt` | `closure_11_5` | as 11.2 | closed, I2 open |
| 11.6 `AnnulusMassBoundByHarmonicChainStmt` | `closure_11_6` | hI2 (as 1.3); hAff hDG hCC hE hW hN (PROPOSED); hL1 hWeyl hE1 hE3 hB (FROZEN) | closed, I2 open |
| 11.7 `ManyConeBadScalesStmt` | `closure_11_7` | hDG hCC hE hNA (PROPOSED); hCamp hDecFrozen hDec hCM (FROZEN) | closed |
| 11.8 `ConeBadEventProbabilityStmt` | `closure_11_8` | hDG hCC hE (PROPOSED) | closed |
| 11.10 `SmallMetricDiameterLargeMassSquareStmt` | `closure_11_10` | FROZEN and PROPOSED (hAx, hShift; detail in `Closure/Sec11.lean`) | closed |
| 11.11 `HarmonicBallNotMetricBallStmt` | `closure_11_11` | as 11.6, plus h13 `ManyPinchScalesStmt` **OPEN** (Lemma 11.13), plus hmetricAxioms (PROPOSED) | conditional on OPEN 11.13 |
| 11.13 `CorrectedLemma11_13Stmt` | `closure_11_13` | hAx, hE (FROZEN, PROPOSED); hStep8 `Step8IdentificationStmt` **OPEN** (`FirstPass/S11i/Corrected11_13.lean:57`) | conditional on OPEN hStep8 |
| 11.14 `PinchEventMetricBallConsequenceStmt` | `closure_11_14` | hAx (FROZEN) | closed |
| 11.15 `PinchFirstEventFaithfulStmt` | `closure_11_15` | hCM hMet hWSC hAx hExists (FROZEN); hAff (PROPOSED) | closed |
| 11.9 `SmallMetricDiameterLargeMassStmt` | `closure_11_9` | FROZEN, PROPOSED and CITED inputs of 11.9 and 11.10 (table in `Closure/Sec11.lean`) | closed |
| 11.12 `CorrectedLemma11_12Stmt` | `closure_11_12` | z4 inputs; hgrowth (I2) **OPEN** (z4 notes); hN2 (FROZEN, kept per operator 04:48) | conditional on OPEN I2 |
| 11.16 `PinchSecondEventFaithfulStmt` | `closure_11_16` | closures 11.15 and 11.9; hholder (CITED, Prop 2.5); FROZEN; PROPOSED hEx hWeyl hNa0 hNa | closed |
| 11.17 `PinchThirdEventFaithfulStmt` | `closure_11_17` | closure 11.16; hN2 (FROZEN) | closed |

## Open items and flags
* 1.2 not yet in this file (table above). Its only missing ingredient is the bridge `manyPinchScales_of_corrected` (z7,
  `Closure/Bridge12.lean`, uncommitted). The printed Lemma 11.13 is then conditional only on the OPEN `hStep8` of `closure_11_13`.
* I2 `LQGVolumeGrowthAllScalesStmt` is a hypothesis of 1.3, 11.2, 11.5, 11.6, and the open derivation is z4's notes.
* Sec11 is committed in full (HEAD, 14 closures); this file builds against that version.
* Commit 85bdd95 (z11) overwrote this file with a Section 1 version whose `closure_1_2` takes `ManyPinchScalesStmt` as an OPEN hypothesis. This version restores the table above (1.2 is added only when the bridge is committed).

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
