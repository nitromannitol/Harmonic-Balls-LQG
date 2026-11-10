import HarmonicBalls.FirstPass.S11
import HarmonicBalls.FirstPass.S11c
import HarmonicBalls.FirstPass.S11i.Corrected11_13
import HarmonicBalls.FirstPass.S11j.FieldAssembly11_15
import HarmonicBalls.FirstPass.S11x

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
| 11.10 (`SmallMetricDiameterLargeMassSquareStmt`, corrected, `HarmonicBalls.S11c.firstPass_11_10`) | `closure_11_10` | FROZEN and Proposed (hAx, hShift) |
| 11.13 (`CorrectedLemma11_13Stmt`, `firstPass_11_13_corrected`) | `closure_11_13` | hAx, hE (Proposed); **OPEN** `hStep8 : Step8IdentificationStmt` (no proof in the repository) |
| 11.14 (`PinchEventMetricBallConsequenceStmt`) | `closure_11_14` | hAx (FROZEN) |
| 11.15 (`PinchFirstEventFaithfulStmt`, corrected) | `closure_11_15` | hCM, hMet, hWSC, haxioms (FROZEN); hAff (Proposed); `hEx` discharged by `lqgMetricExponentPositive_of_inputs` (`FirstPass/S11x.lean:94`), with `hExists` (FROZEN) |

Blocked by a name clash (not closed here): 11.9, 11.16, 11.17 need the 11.9 chain (FirstPass/S11d.lean) and the 11.10 chain (FirstPass/S11c.lean) in one environment, but both declare HarmonicBalls.exists_measurable_exterior_bound (S11c/ExteriorBound.lean:93 and S11d/MeasurableExterior.lean:22). Not closed yet: 11.2, 11.5, 11.6 (need closure_5_5 and closure_8_1), 11.11 (needs Lemma 11.13 in the printed form ManyPinchScalesStmt), 11.12 (pending the firstPass_11_12 of the Lemma 11.12 team).
-/

namespace HarmonicBalls.Closure

open MeasureTheory

universe u

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
which needs the FROZEN `WholePlaneGFFExistsFrozen` and the affine invariance input `WholePlaneGFFAffineInvariance`. -/
theorem closure_11_15
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hWSC : WeylScalingCompositionFrozen.{u}) (hExists : WholePlaneGFFExistsFrozen.{0})
    (hAff : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchFirstEventFaithfulStmt.{u} :=
  firstPass_11_15_corrected hCM hMet hWSC (lqgMetricExponentPositive_of_inputs hExists hAff) hAx

end HarmonicBalls.Closure
