import HarmonicBalls.FirstPass.Closure.PaperExponentOf13
import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.S11i.Final11_13Close
import HarmonicBalls.FirstPass.S8c.BirkhoffDerived
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived

/-! # Counted results 11.x and A.x without the derived frozen inputs

For each counted declaration of result 11.x or A.x that takes
`BirkhoffPointwiseErgodic` or `LocalLQGInsertionWeylOffOrigin` as a binder, this file gives the theorem
`<countedName>_derivedInputs`: the same statement with that binder removed, proved by applying the counted
declaration to the derived theorems `birkhoffPointwiseErgodic_derived` (FirstPass/S8c/BirkhoffDerived.lean)
and `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean). No hypothesis is added. -/

namespace HarmonicBalls.Closure

open MeasureTheory
universe u

/-- Result 11.2, counted declaration `closure_11_2`, with the frozen input
    `BirkhoffPointwiseErgodic`, `LocalLQGInsertionWeylOffOrigin` removed from the binders. The
    removed input is supplied by the derived theorem (`birkhoffPointwiseErgodic_derived`,
    `localLQGInsertionWeylOffOrigin_derived`). Otherwise the statement is that of `closure_11_2`. -/
theorem closure_11_2_derivedInputs
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
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    : HarmonicBallNotLipschitzStmt.{u} :=
  closure_11_2 hDG hCC hE hW hN hL1 (localLQGInsertionWeylOffOrigin_derived.{u}) hE1 hE3
    (birkhoffPointwiseErgodic_derived.{0}) hCamp hDecFrozen hDec hCM

/-- Result 11.5, counted declaration `closure_11_5`, with the frozen input
    `BirkhoffPointwiseErgodic`, `LocalLQGInsertionWeylOffOrigin` removed from the binders. The
    removed input is supplied by the derived theorem (`birkhoffPointwiseErgodic_derived`,
    `localLQGInsertionWeylOffOrigin_derived`). Otherwise the statement is that of `closure_11_5`. -/
theorem closure_11_5_derivedInputs
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
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    : NoConeConditionStmt.{u} :=
  closure_11_5 hDG hCC hE hW hN hL1 (localLQGInsertionWeylOffOrigin_derived.{u}) hE1 hE3
    (birkhoffPointwiseErgodic_derived.{0}) hCamp hDecFrozen hDec hCM

/-- Result 11.6, counted declaration `closure_11_6`, with the frozen input
    `BirkhoffPointwiseErgodic`, `LocalLQGInsertionWeylOffOrigin` removed from the binders. The
    removed input is supplied by the derived theorem (`birkhoffPointwiseErgodic_derived`,
    `localLQGInsertionWeylOffOrigin_derived`). Otherwise the statement is that of `closure_11_6`. -/
theorem closure_11_6_derivedInputs
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
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : AnnulusMassBoundByHarmonicChainStmt.{u} :=
  closure_11_6 hDG hCC hE hW hN hL1 (localLQGInsertionWeylOffOrigin_derived.{u}) hE1 hE3
    (birkhoffPointwiseErgodic_derived.{0})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure

open MeasureTheory Metric Set Filter Topology
universe u

/-- Result 11.11, counted declaration `closure_11_11_paperExponent_of_11_13`, with the frozen input
    `BirkhoffPointwiseErgodic` removed from the binders. The removed input is supplied by the
    derived theorem (`birkhoffPointwiseErgodic_derived`). Otherwise the statement is that of
    `closure_11_11_paperExponent_of_11_13`. -/
theorem closure_11_11_paperExponent_of_11_13_derivedInputs
    (_hDim : WholePlaneLQGGraphDimension)
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
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    : HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  closure_11_11_paperExponent_of_11_13 _hDim hDG hCC hE hW hN hL1 hE1 hE3
    (birkhoffPointwiseErgodic_derived.{0}) hAx h13

end HarmonicBalls.Closure

namespace HarmonicBalls.FirstPassS11iFinal11_13Close

open MeasureTheory
open HarmonicBalls.FirstPassS11iFinal11_13

/-- Result 11.13, counted declaration `firstPass_11_13_closed`, with the frozen input
    `BirkhoffPointwiseErgodic` removed from the binders. The removed input is supplied by the
    derived theorem (`birkhoffPointwiseErgodic_derived`). Otherwise the statement is that of
    `firstPass_11_13_closed`. -/
theorem firstPass_11_13_closed_derivedInputs
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
    (hM2 : WeylShiftedMassMeasurableFrozen.{0})
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
  firstPass_11_13_closed hAx hLen hN2 hμW hLoc hCanonM hNonat hExists hDG hCCα hE hfr hmass hCMAbs
    hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2
    (birkhoffPointwiseErgodic_derived.{0}) hRootCont hProf hWCont hA10 hFull hgrowth hDsm hK

end HarmonicBalls.FirstPassS11iFinal11_13Close
