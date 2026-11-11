import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.Phase2.DerivedInputsSec11A
import HarmonicBalls.FirstPass.Phase2.WeylShiftedMassDerived

/-! # Counted results 11.9, 11.10, 11.13, 11.16, 11.17 without the derived mass-measurability input


For each counted declaration that takes `WeylShiftedMassMeasurableFrozen` as a binder (uses 11.9, 11.10, 11.13, 11.16, 11.17), this file gives the theorem
`<countedName>_derivedInputs2`: the same statement with that binder removed, proved by applying the counted
declaration to `HarmonicBalls.weylShiftedMassMeasurable_derived` (FirstPass/Phase2/WeylShiftedMassDerived.lean).
The counted declarations 11.9, 11.10, 11.16 and 11.17 take no `BirkhoffPointwiseErgodic` and no
`LocalLQGInsertionWeylOffOrigin` binder. The counted declaration of 11.13 is applied through its existing
wrapper `firstPass_11_13_closed_derivedInputs` (DerivedInputsSec11A.lean). No hypothesis is added. -/

namespace HarmonicBalls.Closure

open MeasureTheory
universe u

/-- Result 11.9, counted declaration `closure_11_9`, with the frozen input
    `WeylShiftedMassMeasurableFrozen` removed from the binders. The removed input is supplied by the
    derived theorem (`HarmonicBalls.weylShiftedMassMeasurable_derived`). Otherwise the statement is
    that of `closure_11_9`. -/
theorem closure_11_9_derivedInputs2
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hMass : LQGMassFunctionalMeasurableFrozen.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    : SmallMetricDiameterLargeMassStmt.{u} :=
  closure_11_9 hCM hWSC hMet hMass hShift hFD hAx hDC hCMT hPos hMassM hSupM hFin hW hM1
    (HarmonicBalls.weylShiftedMassMeasurable_derived.{u})

/-- Result 11.10, counted declaration `closure_11_10`, with the frozen input
    `WeylShiftedMassMeasurableFrozen` removed from the binders. The removed input is supplied by the
    derived theorem (`HarmonicBalls.weylShiftedMassMeasurable_derived`). Otherwise the statement is
    that of `closure_11_10`. -/
theorem closure_11_10_derivedInputs2
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen)
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    : SmallMetricDiameterLargeMassSquareStmt.{u} :=
  closure_11_10 hDC hCMT hPos hMassM hSupM hFin hW hShift hM1
    (HarmonicBalls.weylShiftedMassMeasurable_derived.{u}) hAx

/-- Result 11.16, counted declaration `closure_11_16`, with the frozen input
    `WeylShiftedMassMeasurableFrozen` removed from the binders. The removed input is supplied by the
    derived theorem (`HarmonicBalls.weylShiftedMassMeasurable_derived`). Otherwise the statement is
    that of `closure_11_16`. -/
theorem closure_11_16_derivedInputs2
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hWeyl : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hMass : LQGMassFunctionalMeasurableFrozen.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    : PinchSecondEventFaithfulStmt.{u} :=
  closure_11_16 hAx hK1 hholder hEx hWeyl hNa0 hNa hCM hWSC hMet hExists hMass hShift hFD hDC hCMT
    hPos10 hMassM hSupM hFin hW hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived.{u}) hM hDiam
    hMk

/-- Result 11.17, counted declaration `closure_11_17`, with the frozen input
    `WeylShiftedMassMeasurableFrozen` removed from the binders. The removed input is supplied by the
    derived theorem (`HarmonicBalls.weylShiftedMassMeasurable_derived`). Otherwise the statement is
    that of `closure_11_17`. -/
theorem closure_11_17_derivedInputs2
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hWeyl : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hMass : LQGMassFunctionalMeasurableFrozen.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hN2 : WeylScaledEuclideanFrozen)
    : PinchThirdEventFaithfulStmt.{u} :=
  closure_11_17 hAx hK1 hholder hEx hWeyl hNa0 hNa hCM hWSC hMet hExists hMass hShift hFD hDC hCMT
    hPos10 hMassM hSupM hFin hW hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived.{u}) hM hDiam
    hMk hN2

end HarmonicBalls.Closure

namespace HarmonicBalls.FirstPassS11iFinal11_13Close

open MeasureTheory
universe u
open MeasureTheory Metric Set Filter Topology
open HarmonicBalls.FirstPassS11iFinal11_13

/-- Result 11.13, counted declaration `firstPass_11_13_closed`, with the frozen input
    `WeylShiftedMassMeasurableFrozen` removed from the binders. The removed input is supplied by the
    derived theorem (`HarmonicBalls.weylShiftedMassMeasurable_derived`). It is applied to
    `firstPass_11_13_closed_derivedInputs` (DerivedInputsSec11A.lean), which already removes
    `BirkhoffPointwiseErgodic` and `LocalLQGInsertionWeylOffOrigin`. Otherwise the statement is that
    of `firstPass_11_13_closed_derivedInputs`. -/
theorem firstPass_11_13_closed_derivedInputs2
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
    (hShift : LQGMetricContinuousShiftFactI.{0})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hCMT : CameronMartinEventTransferFrozen.{0})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hMassM : LQGMeasureSquareMeasurableFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hFull : LQGMeasureFullSupportStmt.{0})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
  firstPass_11_13_closed_derivedInputs hAx hLen hN2 hμW hLoc hCanonM hNonat hExists hDG hCCα hE hfr
    hmass hCMAbs hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hMassM hSupM hFin hW
    hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived.{0}) hRootCont hProf hWCont hA10 hFull
    hgrowth hDsm hK

end HarmonicBalls.FirstPassS11iFinal11_13Close
