import HarmonicBalls.FirstPass.S11i.Final11_13
import HarmonicBalls.FirstPass.S11i.Step8CalibrationClose
import HarmonicBalls.FirstPass.S11ak.BaseComparison
import HarmonicBalls.FirstPass.S11t

/-!
# Lemma 11.13 (canonical), closed: no OPEN binder (fp-S11-13-final-close, owner n3; Codex ASTRA step 7)

`firstPass_11_13_closed` concludes `CorrectedLemma11_13CanonicalStmt.{0}` from frozen and proposed inputs only. It is
`firstPass_11_13` (`S11i/Final11_13.lean:213`) with its open binder `hCal` replaced by
`step8EventCalibration` (`S11i/Step8CalibrationClose.lean:37`, commit 89f7c26c, n1).

Why a separate module. `S11i/Step8CalibrationClose.lean` imports `S11i/Final11_13.lean` (for the projections
`lqgMetricExponentPositive_derived` and `lqgMetricSatisfiesAxiomsUnivFrozen_zero`). So `Final11_13.lean` cannot import
`Step8CalibrationClose.lean` without an import cycle. This leaf module imports both. The closed theorem can move into
`Final11_13.lean` once `Step8CalibrationClose.lean` imports a module that holds the projections instead (one import line
there, not owned by this task).

Binders: those of `firstPass_11_13` except `hCal`, plus three frozen Draft inputs of `step8EventCalibration`: `hFull` (I1,
`Draft/Section2.lean:109`), `hgrowth` (I2, `Draft/Section2.lean:122`) and `hDsm` (Prop 11.9, `Draft/Section11.lean:201`).
Derived, not binders: `hBase` (`lqgMetricBaseComparison_of_canonical`, `S11ak/BaseComparison.lean:67`, from `hCanonM` by
projection, `hLen`, `hE` at `α₀ = 0`) and `hS` (`PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs`,
`S11t.lean:30`, from `hMf`, `hholder`, `hE`, `hμW`, `hNonat`). The docstring of `PinchSecondAnnulusStep`
(`S11k/BundleParts.lean:40`) still says OPEN; that is stale, since this lemma proves it.

Classes (FROZEN = `docs/campaign/FROZEN.md` or a `Frozen/` file; PROPOSED = `Proposed/` or a Proposed def):
the `firstPass_11_13` list (see its docstring) with `hCal` removed, plus `hFull`, `hgrowth`, `hDsm` (FROZEN).
-/

namespace HarmonicBalls.FirstPassS11iFinal11_13Close

open MeasureTheory
open HarmonicBalls.FirstPassS11iFinal11_13

/-- **Lemma 11.13 (canonical), closed, universe 0.** `CorrectedLemma11_13CanonicalStmt.{0}` from the frozen and proposed
inputs, with no OPEN binder. -/
theorem firstPass_11_13_closed
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hLen : LQGMetricLengthUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hmass : LQGMassFunctionalMeasurableFrozen.{0})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{0})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
    (hMk : DomainMarkovConditionalPositiveFrozen.{0})
    (hholder : GreenPotentialHolderStmt.{0})
    (hShift : LQGMetricContinuousShiftFactI.{0}) (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{0}) (hCMT : CameronMartinEventTransferFrozen.{0})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0}) (hMassM : LQGMeasureSquareMeasurableFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{0}) (hM2 : WeylShiftedMassMeasurableFrozen.{0})
    (hBirk : BirkhoffPointwiseErgodic.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hFull : LQGMeasureFullSupportStmt.{0})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂) :
    CorrectedLemma11_13CanonicalStmt.{0} :=
  firstPass_11_13 hAx hLen hN2 hμW hLoc hCanonM hNonat hExists hDG hCCα hE hfr hmass hCMAbs hCMRew hComp hMf hDiam hMk
    hholder hShift hFD hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2 hBirk hRootCont hProf hWCont hA10
    (HarmonicBalls.S11i.Step8CalibrationClose.step8EventCalibration hAx hLen hN2
      (HarmonicBalls.S11ak.lqgMetricBaseComparison_of_canonical (lqgCanonicalDecodersExist_of_measurable hCanonM) hLen
        (fun γ Ω _ P hC hcirc => hE Ω P γ 0 hC hcirc))
      hμW hLoc hNonat hFull hgrowth hfr hmass hCMAbs hCMRew hComp hDsm hMf hDiam hMk
      (HarmonicBalls.PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs hMf hholder
        (fun γ Ω _ P hC hcirc => hE Ω P γ 0 hC hcirc)
        (fun γ Ω _ P hC hcirc => hμW Ω P γ 0 hC hcirc)
        (fun γ Ω _ P hC hcirc => hNonat γ 0 Ω P hC hcirc)
        (fun γ α Ω _ P hC hcirc => hNonat γ α Ω P hC hcirc))
      hK hRootCont hPos10 hA10 hBirk hProf hWCont hCCα hE hCanonM hExists)
    hK

#print axioms HarmonicBalls.FirstPassS11iFinal11_13Close.firstPass_11_13_closed

end HarmonicBalls.FirstPassS11iFinal11_13Close
