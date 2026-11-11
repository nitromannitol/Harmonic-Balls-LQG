import HarmonicBalls.FirstPass.Phase2.DerivedInputs26
import HarmonicBalls.FirstPass.Phase2.GFFExistsConstructed

/-!
# Round-25 wrappers of the DerivedInputs26 counted forms, with the row-29 existence binder discharged
(task fp-phase2-gff-cov-symm, worker z6)

Each wrapper `..._derivedInputs25` is the counted form `..._derivedInputs26` with its binder
`hExists : WholePlaneGFFExistsFrozen.{0}` (row 29) replaced by the single named input `hB2 : WholePlaneCovPSDStmt`
(B2: the whole-plane covariance is positive semidefinite; MQ-lh-25, still open). The symmetry input is no longer a
binder: `LatticeProb.Gauss.wholePlaneCovSymm_proved` (LPStage/GFFCovSymm.lean) proves `WholePlaneCovSymmStmt`, and
`HarmonicBalls.wholePlaneGFFExistsFrozen_zero_derived_of_psd hB2` (GFFExistsConstructed.lean) gives `hExists`.
Binder count: equal to DerivedInputs26 (`hExists` replaced by `hB2`).
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.Closure

/-- Binder-trade wrapper `closure_1_2_canonical_of_11_13_universe0_derivedInputs25` of `closure_1_2_canonical_of_11_13_universe0_derivedInputs22` (fp-phase2-reducible-trades-di26, worker z7): `hLoc` is discharged by `hDec` (same Prop, as in DerivedInputs23). -/
theorem closure_1_2_canonical_of_11_13_universe0_derivedInputs25
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
    (hB2 : LatticeProb.Gauss.WholePlaneCovPSDStmt)
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
   : HarmonicBallNoveltyCanonicalStmt.{0}

  := HarmonicBalls.Closure.closure_1_2_canonical_of_11_13_universe0_derivedInputs22 (hDG := hDG) (hE := hE)
    (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM) (hAx := hAx) (hTor := hTor)
    (hN2 := hN2) (hLoc := hDec) (hCanonM := hCanonM) (hExists := HarmonicBalls.wholePlaneGFFExistsFrozen_zero_derived_of_psd hB2) (hCC := hCC) (hfr := hfr)
    (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC)
    (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10)
    (hK := hK)

/-- Binder-trade wrapper `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs25` of `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs22` (fp-phase2-reducible-trades-di26, worker z7): `hLoc` is discharged by `hDec` (same Prop, as in DerivedInputs23). -/
theorem closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs25
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
    (hB2 : LatticeProb.Gauss.WholePlaneCovPSDStmt)
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
   : HarmonicBallNoveltyFaithfulStmt.{0}

  := HarmonicBalls.Closure.closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs22 (hDG := hDG)
    (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM) (hAx := hAx)
    (hTor := hTor) (hN2 := hN2) (hLoc := hDec) (hCanonM := hCanonM) (hExists := HarmonicBalls.wholePlaneGFFExistsFrozen_zero_derived_of_psd hB2) (hCC := hCC)
    (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift)
    (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont)
    (hA10 := hA10) (hK := hK)

/-- Binder-trade wrapper `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs25` of `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs22` (fp-phase2-reducible-trades-di26, worker z7): `hLoc` is discharged by `hDec` (same Prop, as in DerivedInputs23). -/
theorem closure_1_2_paperExponent_of_11_13_universe0_derivedInputs25
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
    (hB2 : LatticeProb.Gauss.WholePlaneCovPSDStmt)
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
   : HarmonicBallNoveltyFaithfulStmt.{0}

  := HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13_universe0_derivedInputs22 (_hDim := _hDim)
    (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM)
    (hAx := hAx) (hTor := hTor) (hN2 := hN2) (hLoc := hDec) (hCanonM := hCanonM) (hExists := HarmonicBalls.wholePlaneGFFExistsFrozen_zero_derived_of_psd hB2)
    (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder)
    (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin)
    (hRootCont := hRootCont) (hA10 := hA10) (hK := hK)

/-- Binder-trade wrapper `firstPass_1_2_faithful_universe0_derivedInputs25` of `firstPass_1_2_faithful_universe0_derivedInputs22` (fp-phase2-reducible-trades-di26, worker z7): `hLoc` is discharged by `hDec` (same Prop, as in DerivedInputs23). -/
theorem firstPass_1_2_faithful_universe0_derivedInputs25
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
    (hB2 : LatticeProb.Gauss.WholePlaneCovPSDStmt)
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
   : HarmonicBallNoveltyFaithfulStmt.{0}

  := HarmonicBalls.Closure.firstPass_1_2_faithful_universe0_derivedInputs22 (hDG := hDG) (hE := hE)
    (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM) (hAx := hAx) (hTor := hTor)
    (hN2 := hN2) (hLoc := hDec) (hCanonM := hCanonM) (hExists := HarmonicBalls.wholePlaneGFFExistsFrozen_zero_derived_of_psd hB2) (hCC := hCC) (hfr := hfr)
    (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC)
    (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10)
    (hK := hK)

end HarmonicBalls.Closure

namespace HarmonicBalls.FirstPassS11iFinal11_13

/-- Binder-trade wrapper `firstPass_11_13_derivedInputs25` of `firstPass_11_13_derivedInputs22` (fp-phase2-reducible-trades-di26, worker z7): `_hWCont` is discharged by `HarmonicBalls.weylMetricCompositionContinuousOuter_derived` (as in DerivedInputs23). -/
theorem firstPass_11_13_derivedInputs25
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hB2 : LatticeProb.Gauss.WholePlaneCovPSDStmt)
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (_hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (_hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
   : CorrectedLemma11_13CanonicalStmt.{0}

  := HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_derivedInputs22 (hAx := hAx) (hN2 := hN2)
    (hLoc := hLoc) (hCanonM := hCanonM) (hExists := HarmonicBalls.wholePlaneGFFExistsFrozen_zero_derived_of_psd hB2) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr)
    (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC)
    (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (_hRootCont := _hRootCont)
    (_hWCont := HarmonicBalls.weylMetricCompositionContinuousOuter_derived) (_hA10 := _hA10) (hCal := hCal)
    (hK := hK)

end HarmonicBalls.FirstPassS11iFinal11_13
