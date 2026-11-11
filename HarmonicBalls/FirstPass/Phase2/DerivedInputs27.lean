import HarmonicBalls.FirstPass.Phase2.DerivedInputs26
import HarmonicBalls.FirstPass.Phase2.SquarePositiveDerived

/-!
# Binder trade hPos10

Each wrapper `..._derivedInputs27` is the wrapper `..._derivedInputs26` with the binder `hPos10 : LQGMeasureSquarePositiveFrozen`
(FirstPass/Frozen/S11c.lean:130) removed. The binder is discharged by
`HarmonicBalls.lqgMeasureSquarePositiveFrozen_derived` (Phase2/SquarePositiveDerived.lean), which uses only the existence
inputs `hDG`, `hCC` (at `α₀ = 0`) and `hE`; these are already binders of every wrapper. So the binder count drops by one in
each wrapper, and no new premise is added. All other trades inherited from DerivedInputs22, DerivedInputs23 and
DerivedInputs26 are unchanged.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.Closure

/-- Binder-trade wrapper `closure_1_2_canonical_of_11_13_universe0_derivedInputs27` of `closure_1_2_canonical_of_11_13_universe0_derivedInputs26`: `hLoc` is discharged by `hDec` (same Prop, as in DerivedInputs23). -/
theorem closure_1_2_canonical_of_11_13_universe0_derivedInputs27
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{0})
    (hDec : LocalLQGDecoderCommonFrozen.{0})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hTor : TorhorstSimpleLoopFrozen)
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCC : ∀ (γ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{0} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{0})
    (hholder : GreenPotentialHolderStmt.{0})
    (hShift : LQGMetricContinuousShiftFactI.{0})
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hCMT : CameronMartinEventTransferFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
   : HarmonicBallNoveltyCanonicalStmt.{0}

  := HarmonicBalls.Closure.closure_1_2_canonical_of_11_13_universe0_derivedInputs26 (hDG := hDG) (hE := hE)
    (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM) (hAx := hAx) (hTor := hTor)
    (hN2 := hN2) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr)
    (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC)
    (hCMT := hCMT) (hPos10 := HarmonicBalls.lqgMeasureSquarePositiveFrozen_derived hDG (fun Ω _ P γ hC hcirc => hCC γ 0 Ω P hC hcirc) hE) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10)
    (hK := hK)

/-- Binder-trade wrapper `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs27` of `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs26`: `hLoc` is discharged by `hDec` (same Prop, as in DerivedInputs23). -/
theorem closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs27
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{0})
    (hDec : LocalLQGDecoderCommonFrozen.{0})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hTor : TorhorstSimpleLoopFrozen)
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCC : ∀ (γ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{0} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{0})
    (hholder : GreenPotentialHolderStmt.{0})
    (hShift : LQGMetricContinuousShiftFactI.{0})
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hCMT : CameronMartinEventTransferFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
   : HarmonicBallNoveltyFaithfulStmt.{0}

  := HarmonicBalls.Closure.closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs26 (hDG := hDG)
    (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM) (hAx := hAx)
    (hTor := hTor) (hN2 := hN2) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC)
    (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift)
    (hDC := hDC) (hCMT := hCMT) (hPos10 := HarmonicBalls.lqgMeasureSquarePositiveFrozen_derived hDG (fun Ω _ P γ hC hcirc => hCC γ 0 Ω P hC hcirc) hE) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont)
    (hA10 := hA10) (hK := hK)

/-- Binder-trade wrapper `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs27` of `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs26`: `hLoc` is discharged by `hDec` (same Prop, as in DerivedInputs23). -/
theorem closure_1_2_paperExponent_of_11_13_universe0_derivedInputs27
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{0})
    (hDec : LocalLQGDecoderCommonFrozen.{0})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hTor : TorhorstSimpleLoopFrozen)
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCC : ∀ (γ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{0} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{0})
    (hholder : GreenPotentialHolderStmt.{0})
    (hShift : LQGMetricContinuousShiftFactI.{0})
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hCMT : CameronMartinEventTransferFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
   : HarmonicBallNoveltyFaithfulStmt.{0}

  := HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13_universe0_derivedInputs26 (_hDim := _hDim)
    (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM)
    (hAx := hAx) (hTor := hTor) (hN2 := hN2) (hCanonM := hCanonM) (hExists := hExists)
    (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder)
    (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := HarmonicBalls.lqgMeasureSquarePositiveFrozen_derived hDG (fun Ω _ P γ hC hcirc => hCC γ 0 Ω P hC hcirc) hE) (hSupM := hSupM) (hFin := hFin)
    (hRootCont := hRootCont) (hA10 := hA10) (hK := hK)

/-- Binder-trade wrapper `firstPass_1_2_faithful_universe0_derivedInputs27` of `firstPass_1_2_faithful_universe0_derivedInputs26`: `hLoc` is discharged by `hDec` (same Prop, as in DerivedInputs23). -/
theorem firstPass_1_2_faithful_universe0_derivedInputs27
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{0})
    (hDec : LocalLQGDecoderCommonFrozen.{0})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hTor : TorhorstSimpleLoopFrozen)
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCC : ∀ (γ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{0} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{0})
    (hholder : GreenPotentialHolderStmt.{0})
    (hShift : LQGMetricContinuousShiftFactI.{0})
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hCMT : CameronMartinEventTransferFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
   : HarmonicBallNoveltyFaithfulStmt.{0}

  := HarmonicBalls.Closure.firstPass_1_2_faithful_universe0_derivedInputs26 (hDG := hDG) (hE := hE)
    (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM) (hAx := hAx) (hTor := hTor)
    (hN2 := hN2) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr)
    (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC)
    (hCMT := hCMT) (hPos10 := HarmonicBalls.lqgMeasureSquarePositiveFrozen_derived hDG (fun Ω _ P γ hC hcirc => hCC γ 0 Ω P hC hcirc) hE) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10)
    (hK := hK)

end HarmonicBalls.Closure

namespace HarmonicBalls.FirstPassS11iFinal11_13

/-- Binder-trade wrapper `firstPass_11_13_derivedInputs27` of `firstPass_11_13_derivedInputs26`: `_hWCont` is discharged by `HarmonicBalls.weylMetricCompositionContinuousOuter_derived` (as in DerivedInputs23). -/
theorem firstPass_11_13_derivedInputs27
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (γ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{0} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{0})
    (hholder : GreenPotentialHolderStmt.{0})
    (hShift : LQGMetricContinuousShiftFactI.{0})
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hCMT : CameronMartinEventTransferFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (_hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (_hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
   : CorrectedLemma11_13CanonicalStmt.{0}

  := HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_derivedInputs26 (hAx := hAx) (hN2 := hN2) (hLoc := hLoc)
 (hCanonM := hCanonM) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr)
    (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC)
    (hCMT := hCMT) (hPos10 := HarmonicBalls.lqgMeasureSquarePositiveFrozen_derived hDG (fun Ω _ P γ hC hcirc => hCC γ 0 Ω P hC hcirc) hE) (hSupM := hSupM) (hFin := hFin) (_hRootCont := _hRootCont)
 (_hA10 := _hA10) (hCal := hCal)
    (hK := hK)

end HarmonicBalls.FirstPassS11iFinal11_13
