import HarmonicBalls.FirstPass.S11
import HarmonicBalls.FirstPass.S11c
import HarmonicBalls.FirstPass.S11i.Corrected11_13
import HarmonicBalls.FirstPass.S11j.FieldAssembly11_15
import HarmonicBalls.FirstPass.S11x
import HarmonicBalls.FirstPass.Closure.Sec6
import HarmonicBalls.FirstPass.Closure.SecA45
import HarmonicBalls.FirstPass.Closure.Sec78910
import HarmonicBalls.FirstPass.S11d
import HarmonicBalls.FirstPass.S11h.PinchCertificateProof11_17
import HarmonicBalls.FirstPass.S11k.FirstLExterior
import HarmonicBalls.FirstPass.S11m.Final11_12

/-!
# Closure of the counted Section 11 results (fp-closure-11, owner z11)

Each `closure_11_k` concludes exactly the conclusion of the counted first-pass theorem of Lemma/Proposition 11.k
and takes as hypotheses only FIRST-PASS FROZEN Props, Proposed/External Props and the cited `GreenPotentialHolderStmt`
(Proposition 2.5, Green clause). Paper-owned hypotheses are discharged by the closure of their result, recursively.
Universe `u`; the axiom-form hypothesis `LQGMetricFieldAxiomsUnivFrozen` is adapted to the binder order of each
`firstPass` theorem by a lambda (no new mathematics).

| result | closure | remaining hypotheses (class) |
|---|---|---|
| 11.7 (`ManyConeBadScalesStmt`, corrected, `HarmonicBalls.S11c.firstPass_11_7`) | `closure_11_7` | hDG, hCC, hE, hNA (Proposed); hCamp, hDecFrozen, hDec, hCM (FROZEN) |
| 11.8 (`ConeBadEventProbabilityStmt`) | `closure_11_8` | hDG, hCC, hE (Proposed) |
| 11.9 (`SmallMetricDiameterLargeMassStmt`) | `closure_11_9` | frozen, Proposed and cited inputs of 11.9 and 11.10 |
| 11.12 (`CorrectedLemma11_12Stmt`, z4) | `closure_11_12` | `firstPass_11_12_final` (72bf417): FROZEN inputs, Proposed hDG hCC hE hμW hNonat, cited hholder; I2 and affine invariance discharged inside z4's theorem; hN2 kept (operator 04:48) |
| 11.16 (`PinchSecondEventFaithfulStmt`, corrected) | `closure_11_16` | closures 11.15 and 11.9; FROZEN; hholder (cited); Proposed hEx, hWeyl, hNa0, hNa |
| 11.17 (`PinchThirdEventFaithfulStmt`, corrected) | `closure_11_17` | closure 11.16; hN2 (FROZEN) |
| 11.11 (`HarmonicBallNotMetricBallStmt`) | `closure_11_11` | closure_11_6 hypotheses; h13 = printed ManyPinchScalesStmt **OPEN**; hmetricAxioms (Proposed) |
| 11.2 (`HarmonicBallNotLipschitzStmt`) | `closure_11_2` | as closure_11_5 |
| 11.5 (`NoConeConditionStmt`) | `closure_11_5` | closure_11_6 and closure_11_7 hypotheses; I2 discharged by `volumeGrowthI2_of_staged` |
| 11.6 (`AnnulusMassBoundByHarmonicChainStmt`) | `closure_11_6` | hDG, hCC, hE, hW, hN (Proposed; I2 and affine invariance discharged); hL1, hWeyl, hE1, hE3, hB (inputs of 5.5 and 8.1) |
| 11.10 (`SmallMetricDiameterLargeMassSquareStmt`, corrected, `HarmonicBalls.S11c.firstPass_11_10`) | `closure_11_10` | FROZEN and Proposed (hAx, hShift) |
| 11.13 (`CorrectedLemma11_13Stmt`, `firstPass_11_13_corrected`) | `closure_11_13` | hAx, hE (Proposed); **OPEN** `hStep8 : Step8IdentificationStmt` (no proof in the repository) |
| 11.14 (`PinchEventMetricBallConsequenceStmt`) | `closure_11_14` | hAx (FROZEN) |
| 11.15 (`PinchFirstEventFaithfulStmt`, corrected) | `closure_11_15` | hCM, hMet, hWSC, haxioms (FROZEN); affine invariance discharged by `affineInvariance_proved_input`; `hEx` discharged by `lqgMetricExponentPositive_of_inputs` (`FirstPass/S11x.lean:94`), with `hExists` (FROZEN) |

Status: all 14 counted Section 11 results have closure theorems. OPEN (paper-owned, no proof in the repository, kept as
hypotheses): h13 = printed `ManyPinchScalesStmt` (Lemma 11.13) in `closure_11_11`; `hStep8 = Step8IdentificationStmt` in
`closure_11_13`. The volume-growth input I2 and affine invariance are discharged, not open. The S11c/S11d name clash is
resolved (commit 6d75c22 renames the S11d declaration to exists_measurable_internal_metric_bound).
-/

namespace HarmonicBalls.Closure

open MeasureTheory

universe u

/-- Input I2 (`LQGVolumeGrowthAllScalesStmt`) from the Proposed staged inputs `hDG hCC hW hE hN`, by
`HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs` (`Proofs/Sec9/NumberedResultsAssembly.lean:43`), with
the Proposed `LQGMeasureCoordChange` and `LQGMeasureExistence` at alpha0 = 0 (the lemma's binders). Not an open input. -/
theorem volumeGrowthI2_of_staged
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    LQGVolumeGrowthAllScalesStmt.{u} :=
  HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs hDG
    (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hW (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN

/-- Affine invariance of the whole-plane GFF, proved: `HarmonicBalls.wholePlaneGFFAffineInvariance_proved`
(`Proofs/Sec9/AffineInvarianceAssembly.lean:21`), as in `Closure/SecA45.lean`. Universe-polymorphic in `Ω` so that it
serves both `Ω : Type u` and `Ω : Type` hypotheses. -/
theorem affineInvariance_proved_input.{v} : ∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc :=
  fun _ _ P hC hcirc => HarmonicBalls.wholePlaneGFFAffineInvariance_proved P hC hcirc

/-- **Closure of Lemma 11.8** (`ConeBadEventProbabilityStmt`, `firstPass_11_8`). Remaining hypotheses: the Proposed
inputs `WholePlaneLQGBallMassBounds` (Ding-Gwynne), `LQGMeasureCoordChange` (α₀ = 0) and `LQGMeasureExistence`. -/
theorem closure_11_8
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ConeBadEventProbabilityStmt.{u} :=
  firstPass_11_8 hDG hCC hE

/-- **Closure of Lemma 11.7** (`ManyConeBadScalesStmt`, corrected form `HarmonicBalls.S11c.firstPass_11_7`). Its
paper-owned hypothesis `ConeBadEventProbabilityStmt` (Lemma 11.8) is discharged by `closure_11_8`. -/
theorem closure_11_7
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hCC : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α₀ hC hcirc)
    (hNA : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ManyConeBadScalesStmt.{u} :=
  HarmonicBalls.S11c.firstPass_11_7
    (closure_11_8 hDG (fun Ω _ P γ hC hcirc => hCC γ 0 Ω P hC hcirc)
      (fun Ω _ P γ α hC hcirc => hE γ α Ω P hC hcirc))
    hCamp hDecFrozen hDec hCM hCC hE hNA

/-- **Closure of Lemma 11.10** (`SmallMetricDiameterLargeMassSquareStmt`, corrected form `HarmonicBalls.S11c.firstPass_11_10`).
Remaining hypotheses: FIRST-PASS FROZEN inputs and the axiom form `LQGMetricFieldAxiomsUnivFrozen`. -/
theorem closure_11_10
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen) (hShift : LQGMetricContinuousShiftFactI.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  HarmonicBalls.S11c.firstPass_11_10 hDC hCMT hPos hMassM hSupM hFin hW hShift hM1 hM2
    (fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc)

/-- **Closure of Lemma 11.13, corrected form** (`CorrectedLemma11_13Stmt`, `firstPass_11_13_corrected`). The
specialisation `LQGMeasureExistence P γ γ` is taken from the general `hE`. The named input `Step8IdentificationStmt`
(Step 8 of the corrected proof, `FirstPass/S11i/Corrected11_13.lean:57`) has no proof in the repository: it stays a
hypothesis, **OPEN**. -/
theorem closure_11_13
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hStep8 : Step8IdentificationStmt.{u}) :
    CorrectedLemma11_13Stmt.{u} :=
  firstPass_11_13_corrected (fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc)
    (fun γ Ω _ P hC hcirc => hE Ω P γ γ hC hcirc) hStep8

/-- **Closure of Lemma 11.14** (`PinchEventMetricBallConsequenceStmt`, `firstPass_11_14`). Remaining hypothesis: the
FIRST-PASS FROZEN axiom form `LQGMetricFieldAxiomsUnivFrozen`. -/
theorem closure_11_14 (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchEventMetricBallConsequenceStmt.{u} :=
  firstPass_11_14 hAx

/-- **Closure of Lemma 11.15, corrected form** (`PinchFirstEventFaithfulStmt`, `firstPass_11_15_corrected`). The
hypothesis `LQGMetricExponentPositive` is discharged by `lqgMetricExponentPositive_of_inputs` (`FirstPass/S11x.lean:94`),
which needs the FROZEN `WholePlaneGFFExistsFrozen` and the affine invariance `WholePlaneGFFAffineInvariance`, discharged by
`affineInvariance_proved_input` (`HarmonicBalls.wholePlaneGFFAffineInvariance_proved`). -/
theorem closure_11_15
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hWSC : WeylScalingCompositionFrozen.{u}) (hExists : WholePlaneGFFExistsFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchFirstEventFaithfulStmt.{u} :=
  firstPass_11_15_corrected hCM hMet hWSC
    (lqgMetricExponentPositive_of_inputs hExists affineInvariance_proved_input) hAx


/-- **Closure of Lemma 11.6** (`AnnulusMassBoundByHarmonicChainStmt`, `firstPass_11_6`). Paper-owned hypotheses:
`AnnulusMassBoundByOdometerStmt` (Lemma 6.8) and `OdometerBoundByAnnulusMassStmt` (Lemma 6.10), discharged by the
`closure_6_8`, `closure_6_10` (`FirstPass/Closure/Sec6.lean`); `BoundaryMeasureZeroOfCompactClusterStmt`
(Proposition 8.1) by `closure_8_1` (`FirstPass/Closure/Sec78910.lean`); `ExistenceHarmonicBallsStmt` (Proposition 5.5)
by `closure_5_5` (`FirstPass/Closure/SecA45.lean`). Input I2 (`LQGVolumeGrowthAllScalesStmt`) is discharged by
`volumeGrowthI2_of_staged` (`HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs`), and affine invariance by
`affineInvariance_proved_input`. Remaining: the Proposed `LQGMeasureCoordChange`, `LQGMeasureExistence`,
`LQGMeasureWeylScaling`, `LQGMeasureNonatomic`, `WholePlaneLQGBallMassBounds`, and the inputs of 5.5 and 8.1. -/
theorem closure_11_6
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) :
    AnnulusMassBoundByHarmonicChainStmt.{u} :=
  firstPass_11_6 (volumeGrowthI2_of_staged hDG hCC hW hE hN)
    (closure_6_8 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE)
    (closure_6_10 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE)
    (closure_8_1 hL1 hWeyl hE1 hE3 hB hDG affineInvariance_proved_input hCC hW hE hN)
    (closure_5_5 hDG hCC hE hW hN hL1 hWeyl hE1 hE3 hB) affineInvariance_proved_input hCC

/-- **Closure of Lemma 11.5** (`NoConeConditionStmt`, `firstPass_11_5`). Paper-owned hypotheses: Lemma 11.6 (closure
`closure_11_6`) and Lemma 11.7 (closure `closure_11_7`, corrected form). Remaining: the hypotheses of 11.6 and of 11.7
(FROZEN `LocalCampbellMarkedRestrictionFrozen`, `LQGMeasureOfProfileMeasurableFrozen`, `LocalLQGDecoderCommonFrozen`,
`CameronMartinLocallyLipschitzShiftAbsCont`); the input I2 is discharged by `volumeGrowthI2_of_staged`. -/
theorem closure_11_5
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u}) :
    NoConeConditionStmt.{u} :=
  firstPass_11_5
    (closure_11_6 hDG hCC hE hW hN hL1 hWeyl hE1 hE3 hB)
    (closure_11_7 hDG hCamp hDecFrozen hDec hCM
      (fun γ α₀ Ω _ P hC hcirc => hCC Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hE Ω P γ α₀ hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => hN Ω P γ α₀ hC hcirc))
    (volumeGrowthI2_of_staged hDG hCC hW hE hN)

/-- **Closure of Proposition 11.2** (`HarmonicBallNotLipschitzStmt`, `firstPass_11_2`). Its only paper-owned hypothesis,
`NoConeConditionStmt` (Lemma 11.5), is discharged by `closure_11_5`. Remaining hypotheses: those of `closure_11_5`. -/
theorem closure_11_2
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u}) :
    HarmonicBallNotLipschitzStmt.{u} :=
  firstPass_11_2
    (closure_11_5 hDG hCC hE hW hN hL1 hWeyl hE1 hE3 hB hCamp hDecFrozen hDec hCM)

/-- **Closure of Proposition 11.11** (`HarmonicBallNotMetricBallStmt`, `firstPass_11_11`). Paper-owned hypotheses:
`AnnulusMassBoundByHarmonicChainStmt` (Lemma 11.6), discharged by `closure_11_6`, and `ManyPinchScalesStmt`
(Lemma 11.13 in its PRINTED form), which is **OPEN**: the repository proves only the corrected form
`CorrectedLemma11_13Stmt` (`firstPass_11_13_corrected`, closure `closure_11_13`, itself conditional on the OPEN
`Step8IdentificationStmt`), and no bridge from the corrected form to the printed one exists (the printed statement
quantifies one pinch configuration, the corrected one all buffered geometries; a bridge would need an explicit
buffered geometry). Remaining: the hypotheses of `closure_11_6` (I2 discharged by `volumeGrowthI2_of_staged`) and `hmetricAxioms` (Proposed). -/
theorem closure_11_11
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (h13 : ManyPinchScalesStmt.{u})
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11 (closure_11_6 hDG hCC hE hW hN hL1 hWeyl hE1 hE3 hB) h13
    (volumeGrowthI2_of_staged hDG hCC hW hE hN) hmetricAxioms

/-- **Closure of Proposition 11.9** (`SmallMetricDiameterLargeMassStmt`, `firstPass_11_9`). Its paper-owned hypothesis
`SmallMetricDiameterLargeMassSquareStmt` (Lemma 11.10) is discharged by `closure_11_10`. -/
theorem closure_11_9
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hMass : LQGMassFunctionalMeasurableFrozen.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u}) (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u}) :
    SmallMetricDiameterLargeMassStmt.{u} :=
  firstPass_11_9 hCM hWSC hMet hMass hShift hFD
    (fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc)
    (closure_11_10 hDC hCMT hPos hMassM hSupM hFin hW hShift hM1 hM2 hAx)

/-- **Closure of Lemma 11.16, corrected form** (`PinchSecondEventFaithfulStmt`, `firstPass_11_16_corrected`). Its
paper-owned hypotheses are discharged: `PinchFirstEventFaithfulStmt` by `closure_11_15` and
`SmallMetricDiameterLargeMassStmt` by `closure_11_9`. Remaining: FROZEN inputs, the cited `GreenPotentialHolderStmt`
(Proposition 2.5, Green clause), and the Proposed inputs `hEx`, `hWeyl`, `hNa0`, `hNa`. -/
theorem closure_11_16
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hWeyl : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hExists : WholePlaneGFFExistsFrozen.{0})
    (hMass : LQGMassFunctionalMeasurableFrozen.{u}) (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hM : LQGMassInnerMeasurableFrozen.{u}) (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  firstPass_11_16_corrected hAx hK1 hholder hEx hWeyl hNa0 hNa
    (closure_11_15 hCM hMet hWSC hExists hAx)
    (closure_11_9 hCM hWSC hMet hMass hShift hFD hAx hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2)
    hM hDiam hMk

/-- **Closure of Lemma 11.17, corrected form** (`PinchThirdEventFaithfulStmt`, `firstPass_11_17_corrected`). Its
paper-owned hypothesis `PinchSecondEventFaithfulStmt` (Lemma 11.16) is discharged by `closure_11_16`; the other
hypotheses are FROZEN (`hN2 : WeylScaledEuclideanFrozen`) or those of 11.16. -/
theorem closure_11_17
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hWeyl : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hExists : WholePlaneGFFExistsFrozen.{0})
    (hMass : LQGMassFunctionalMeasurableFrozen.{u}) (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hM : LQGMassInnerMeasurableFrozen.{u}) (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hN2 : WeylScaledEuclideanFrozen) :
    PinchThirdEventFaithfulStmt.{u} :=
  firstPass_11_17_corrected
    (closure_11_16 hAx hK1 hholder hEx hWeyl hNa0 hNa hCM hWSC hMet hExists hMass hShift hFD
      hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2 hM hDiam hMk)
    hAx hCM hWSC hMet hMass hK1 hN2


/-- **Closure of Lemma 11.12, corrected form** (`CorrectedLemma11_12Stmt`, `HarmonicBalls.S11m.Final11_12.firstPass_11_12_final`,
z4, commit 72bf417). The paper-owned hypothesis `SmallMetricDiameterLargeMassStmt` (Proposition 11.9) is discharged by
`closure_11_9`. Remaining: the FROZEN inputs of z4's theorem (hAx, hLen, hN2, hLoc, hCanon, hNonat, hExists, hfr, hmass,
hCMAbs, hCMRew, hComp, hMf, hDiam, hMk, and the closure_11_9 inputs); the Proposed inputs `LQGMeasureWeylScaling` (hμW),
`LQGMeasureNonatomicAll` (hNonat), `WholePlaneLQGBallMassBounds` (hDG), `LQGMeasureCoordChange` (hCC) and
`LQGMeasureExistence` (hE); the cited `GreenPotentialHolderStmt` (hholder). The input I2 and the affine invariance are
discharged inside z4's theorem (no hypothesis here). -/
theorem closure_11_12
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u}) (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u}) :
    CorrectedLemma11_12Stmt.{u} :=
  HarmonicBalls.S11m.Final11_12.firstPass_11_12_final hAx hLen hN2 hμW hLoc hCanon hNonat hExists hDG hCC hE
    hfr hmass hCMAbs hCMRew hComp
    (closure_11_9 hCMAbs hComp hfr hmass hShift hFD hAx hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2)
    hMf hDiam hMk hholder

end HarmonicBalls.Closure
