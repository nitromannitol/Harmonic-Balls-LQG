import HarmonicBalls.FirstPass.Phase2.DerivedInputs19
import HarmonicBalls.FirstPass.Phase2.DerivedInputs20
import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived

/-!
# Derived inputs

Wrappers of the DerivedInputs19 and DerivedInputs20 wrappers with the binders of row 33
(`LQGMassInnerMeasurableFrozen`) and row 49 (`LQGMeasureLocality`, forall-closed) discharged by
`lqgMassInnerMeasurable_derived'` and `lqgMeasureLocality_derived` (CircleAverageLocalityLinkDerived.lean).
Row 22 (`LQGMeasureSquareMeasurableFrozen`) is not a binder of these wrappers. Same conclusions. -/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.Closure

/-- Binder-trade wrapper `closure_1_3_derivedInputs21` of the counted form `closure_1_3`: the binders hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_1_3_derivedInputs19`. No binder is added. -/
theorem closure_1_3_derivedInputs21
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : HarmonicBallLocalSetStmt.{u} :=
    HarmonicBalls.Closure.closure_1_3_derivedInputs17 (hmeasure := (HarmonicBalls.lqgMeasureLocality_derived.{u})) (hL1 := hL1)
    (hE3 := hE3) (hDG := hDG) (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))

/-- Binder-trade wrapper `closure_11_16_derivedInputs21` of the counted form `closure_11_16`: the binders hM, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_11_16_derivedInputs19`. No binder is added. -/
theorem closure_11_16_derivedInputs21
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    : PinchSecondEventFaithfulStmt.{u} :=
    HarmonicBalls.Closure.closure_11_16_derivedInputs17 (hAx := hAx) (hK1 := hK1)
    (hholder := hholder) (hEx := hEx) (hNa0 := hNa0) (hNa := hNa) (hWSC := hWSC) (hMet := hMet)
    (hExists := hExists) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10)
    (hSupM := hSupM) (hFin := hFin) (hM1 := hM1) (hM := (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u}))
    (hDiam := (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived hFA)) (hMk := hMk)
    (hmeasure := (HarmonicBalls.lqgMeasureLocality_derived.{u}))

/-- Binder-trade wrapper `closure_11_17_derivedInputs21` of the counted form `closure_11_17`: the binders hM, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_11_17_derivedInputs19`. No binder is added. -/
theorem closure_11_17_derivedInputs21
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    : PinchThirdEventFaithfulStmt.{u} :=
    HarmonicBalls.Closure.closure_11_17_derivedInputs17 (hAx := hAx) (hK1 := hK1)
    (hholder := hholder) (hEx := hEx) (hNa0 := hNa0) (hNa := hNa) (hWSC := hWSC) (hMet := hMet)
    (hExists := hExists) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10)
    (hSupM := hSupM) (hFin := hFin) (hM1 := hM1) (hM := (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u}))
    (hDiam := (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived hFA)) (hMk := hMk)
    (hmeasure := (HarmonicBalls.lqgMeasureLocality_derived.{u}))

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Filter Topology Set Metric

/-- Binder-trade wrapper `closure_11_11_canonical_of_11_13_universe0_derivedInputs21` of the counted form `closure_11_11_canonical_of_11_13_universe0`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_11_11_canonical_of_11_13_universe0_derivedInputs20`. No binder is added. -/
theorem closure_11_11_canonical_of_11_13_universe0_derivedInputs21
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_11_11_canonical_of_11_13_universe0_derivedInputs14 hDG hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    hE3 hAx hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCC) hE)
    hExists hCC hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) HarmonicBalls.weylMetricCompositionContinuousOuter_derived hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.lqgMeasureLocality_derived.{0})) hK (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs21` of the counted form `closure_11_11_paperExponent_of_11_13_universe0`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs20`. No binder is added. -/
theorem closure_11_11_paperExponent_of_11_13_universe0_derivedInputs21
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_11_11_paperExponent_of_11_13_universe0_derivedInputs14 _hDim hDG
    hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hAx hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCC) hE)
    hExists hCC hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) HarmonicBalls.weylMetricCompositionContinuousOuter_derived hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.lqgMeasureLocality_derived.{0})) hK (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `closure_1_2_canonical_of_11_13_universe0_derivedInputs21` of the counted form `closure_1_2_canonical_of_11_13_universe0`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_1_2_canonical_of_11_13_universe0_derivedInputs20`. No binder is added. -/
theorem closure_1_2_canonical_of_11_13_universe0_derivedInputs21
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
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNoveltyCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_canonical_of_11_13_universe0_derivedInputs14 hDG (HarmonicBalls.WholePlaneGFFAffineInvariance_derived) hE hL1
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hCamp hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCC) hE)
    hExists hCC hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) HarmonicBalls.weylMetricCompositionContinuousOuter_derived hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.lqgMeasureLocality_derived.{0})) hK (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs21` of the counted form `closure_1_2_faithful_canonical_of_11_13_universe0`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs20`. No binder is added. -/
theorem closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs21
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
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs14 hDG (HarmonicBalls.WholePlaneGFFAffineInvariance_derived)
    hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hCamp hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCC) hE)
    hExists hCC hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) HarmonicBalls.weylMetricCompositionContinuousOuter_derived hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.lqgMeasureLocality_derived.{0})) hK (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs21` of the counted form `closure_1_2_paperExponent_of_11_13_universe0`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs20`. No binder is added. -/
theorem closure_1_2_paperExponent_of_11_13_universe0_derivedInputs21
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
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13_universe0_derivedInputs14 _hDim hDG
    (HarmonicBalls.WholePlaneGFFAffineInvariance_derived) hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hCamp hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCC) hE)
    hExists hCC hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) HarmonicBalls.weylMetricCompositionContinuousOuter_derived hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.lqgMeasureLocality_derived.{0})) hK (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Filter Topology Set Metric

/-- Binder-trade wrapper `firstPass_11_11_faithful_universe0_derivedInputs21` of the counted form `firstPass_11_11_faithful_universe0`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `firstPass_11_11_faithful_universe0_derivedInputs20`. No binder is added. -/
theorem firstPass_11_11_faithful_universe0_derivedInputs21
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.firstPass_11_11_faithful_universe0_derivedInputs14 hDG hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hAx
    hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCC) hE)
    hExists hCC hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) HarmonicBalls.weylMetricCompositionContinuousOuter_derived hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.lqgMeasureLocality_derived.{0})) hK (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.Closure

namespace HarmonicBalls.FirstPassS11iFinal11_13Close
open MeasureTheory Metric Set Filter Topology
open HarmonicBalls.FirstPassS11iFinal11_13

/-- Binder-trade wrapper `firstPass_11_13_closed_derivedInputs21` of the counted form `firstPass_11_13_closed`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `firstPass_11_13_closed_derivedInputs20`. No binder is added. -/
theorem firstPass_11_13_closed_derivedInputs21
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13Close.firstPass_11_13_closed_derivedInputs14 hAx hN2 hLoc
    hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCC) hE)
    hExists hDG hCC hE hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1
    hRootCont (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) HarmonicBalls.weylMetricCompositionContinuousOuter_derived hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.lqgMeasureLocality_derived.{0})) hK (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.FirstPassS11iFinal11_13Close

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `firstPass_1_2_faithful_universe0_derivedInputs21` of the counted form `firstPass_1_2_faithful_universe0`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `firstPass_1_2_faithful_universe0_derivedInputs20`. No binder is added. -/
theorem firstPass_1_2_faithful_universe0_derivedInputs21
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
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.firstPass_1_2_faithful_universe0_derivedInputs14 hDG hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hCamp
    hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCC) hE)
    hExists hCC hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) HarmonicBalls.weylMetricCompositionContinuousOuter_derived hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.lqgMeasureLocality_derived.{0})) hK (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Binder-trade wrapper `closure_11_11_canonical_derivedInputs21` of the counted form `closure_11_11_canonical`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_11_11_canonical_derivedInputs20`. No binder is added. -/
theorem closure_11_11_canonical_derivedInputs21
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : HarmonicBallNotMetricBallCanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_11_canonical_derivedInputs14 hDG hCC hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hAx hN2
    hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_univ hCC) hE)
    hExists hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId
    (HarmonicBalls.lqgMeasureLocality_derived.{u})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology

/-- Binder-trade wrapper `closure_11_11_paperExponent_derivedInputs21` of the counted form `closure_11_11_paperExponent`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_11_11_paperExponent_derivedInputs20`. No binder is added. -/
theorem closure_11_11_paperExponent_derivedInputs21
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : HarmonicBallNotMetricBallCanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_11_paperExponent_derivedInputs14 _hDim hDG hCC hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3
    hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_univ hCC) hE)
    hExists hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId
    (HarmonicBalls.lqgMeasureLocality_derived.{u})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory

/-- Binder-trade wrapper `closure_11_12_derivedInputs21` of the counted form `closure_11_12`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_11_12_derivedInputs20`. No binder is added. -/
theorem closure_11_12_derivedInputs21
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    : CorrectedLemma11_12Stmt.{u} :=
    HarmonicBalls.Closure.closure_11_12_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u})
    (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) (HarmonicBalls.lqgMeasureLocality_derived.{u})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `closure_11_12_clean_derivedInputs21` of the counted form `closure_11_12_clean`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_11_12_clean_derivedInputs20`. No binder is added. -/
theorem closure_11_12_clean_derivedInputs21
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    : CorrectedLemma11_12CleanStmt.{u} :=
    HarmonicBalls.Closure.closure_11_12_clean_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u})
    (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) (HarmonicBalls.lqgMeasureLocality_derived.{u})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory

/-- Binder-trade wrapper `closure_11_13_canonical_derivedInputs21` of the counted form `closure_11_13_canonical`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_11_13_canonical_derivedInputs20`. No binder is added. -/
theorem closure_11_13_canonical_derivedInputs21
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : CorrectedLemma11_13CanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_13_canonical_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u})
    (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId (HarmonicBalls.lqgMeasureLocality_derived.{u})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology

/-- Binder-trade wrapper `closure_11_13_paperExponent_derivedInputs21` of the counted form `closure_11_13_paperExponent`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_11_13_paperExponent_derivedInputs20`. No binder is added. -/
theorem closure_11_13_paperExponent_derivedInputs21
    (_hDim : WholePlaneLQGGraphDimension)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : CorrectedLemma11_13CanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_13_paperExponent_derivedInputs14 _hDim hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u})
    (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId (HarmonicBalls.lqgMeasureLocality_derived.{u})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure

/-- Binder-trade wrapper `closure_1_2_canonical_derivedInputs21` of the counted form `closure_1_2_canonical`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_1_2_canonical_derivedInputs20`. No binder is added. -/
theorem closure_1_2_canonical_derivedInputs21
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyCanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_1_2_canonical_derivedInputs14 hDG (HarmonicBalls.WholePlaneGFFAffineInvariance_derived) hCC hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hCamp
    hDec hCM hAx hN2 hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_univ hCC) hE)
    hExists hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId hTor
    (HarmonicBalls.lqgMeasureLocality_derived.{u})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure

/-- Binder-trade wrapper `closure_1_2_faithful_canonical_derivedInputs21` of the counted form `closure_1_2_faithful_canonical`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_1_2_faithful_canonical_derivedInputs20`. No binder is added. -/
theorem closure_1_2_faithful_canonical_derivedInputs21
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyFaithfulStmt.{u} :=
    HarmonicBalls.Closure.closure_1_2_faithful_canonical_derivedInputs14 hDG (HarmonicBalls.WholePlaneGFFAffineInvariance_derived) hCC hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3
    hCamp hDec hCM hAx hN2 hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_univ hCC) hE)
    hExists hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId hTor
    (HarmonicBalls.lqgMeasureLocality_derived.{u})

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology

/-- Binder-trade wrapper `closure_1_2_paperExponent_derivedInputs21` of the counted form `closure_1_2_paperExponent`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `closure_1_2_paperExponent_derivedInputs20`. No binder is added. -/
theorem closure_1_2_paperExponent_derivedInputs21
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyFaithfulStmt.{u} :=
    HarmonicBalls.Closure.closure_1_2_paperExponent_derivedInputs14 _hDim hDG (HarmonicBalls.WholePlaneGFFAffineInvariance_derived) hCC hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    hE3 hCamp hDec hCM hAx hN2 hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_univ hCC) hE)
    hExists hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId hTor
    (HarmonicBalls.lqgMeasureLocality_derived.{u})

end HarmonicBalls.Closure

namespace HarmonicBalls.S11m.Clean11_12
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `firstPass_11_12_clean_derivedInputs21` of the counted form `firstPass_11_12_clean`: the binders hMf are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `firstPass_11_12_clean_derivedInputs20`. No binder is added. -/
theorem firstPass_11_12_clean_derivedInputs21
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    : CorrectedLemma11_12CleanStmt.{u} :=
    HarmonicBalls.S11m.Clean11_12.firstPass_11_12_clean_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr (HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived) (HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived)
    hComp hDsm (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder

end HarmonicBalls.S11m.Clean11_12

namespace HarmonicBalls.S11m.Final11_12
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Binder-trade wrapper `firstPass_11_12_final_derivedInputs21` of the counted form `firstPass_11_12_final`: the binders hMf are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `firstPass_11_12_final_derivedInputs20`. No binder is added. -/
theorem firstPass_11_12_final_derivedInputs21
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    : CorrectedLemma11_12Stmt.{u} :=
    HarmonicBalls.S11m.Final11_12.firstPass_11_12_final_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr (HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived) (HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived)
    hComp hDsm (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder

end HarmonicBalls.S11m.Final11_12

namespace HarmonicBalls.FirstPassS11iFinal11_13
open MeasureTheory

/-- Binder-trade wrapper `firstPass_11_13_derivedInputs21` of the counted form `firstPass_11_13`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `firstPass_11_13_derivedInputs20`. No binder is added. -/
theorem firstPass_11_13_derivedInputs21
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (_hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (_hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (_hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_derivedInputs14 hAx hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCC) hE)
    hExists hDG hCC hE hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1
    (HarmonicBalls.weylShiftedMassMeasurable_derived) (HarmonicBalls.birkhoffPointwiseErgodic_derived) _hRootCont (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) _hWCont _hA10 hCal hK (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.FirstPassS11iFinal11_13

namespace HarmonicBalls.FirstPassS11iAssembly11_13
open MeasureTheory

/-- Binder-trade wrapper `firstPass_11_13_canonical_derivedInputs21` of the counted form `firstPass_11_13_canonical`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `firstPass_11_13_canonical_derivedInputs20`. No binder is added. -/
theorem firstPass_11_13_canonical_derivedInputs21
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : CorrectedLemma11_13CanonicalStmt.{u} :=
    HarmonicBalls.FirstPassS11iAssembly11_13.firstPass_11_13_canonical_derivedInputs14 hAx hN2 hLoc
    hCanon (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr hComp
    (HarmonicBalls.lqgMassInnerMeasurable_derived'.{u}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{u} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId (HarmonicBalls.lqgMeasureLocality_derived.{u})

end HarmonicBalls.FirstPassS11iAssembly11_13

namespace HarmonicBalls.FirstPassS11iFinal11_13
open MeasureTheory

/-- Binder-trade wrapper `firstPass_11_13_final_derivedInputs21` of the counted form `firstPass_11_13_final`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `firstPass_11_13_final_derivedInputs20`. No binder is added. -/
theorem firstPass_11_13_final_derivedInputs21
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanon : LQGCanonicalDecodersExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC0 : HarmonicBalls.FirstPassS11iStep8PhysExists.CoordChangeZeroStmt)
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
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hIns : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferStmt)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_zeroStmt hCC0) hE)
    hExists hDG hCC0 hE hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1
    (HarmonicBalls.weylShiftedMassMeasurable_derived) hCal hIns (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.FirstPassS11iFinal11_13

namespace HarmonicBalls.FirstPassS11iFinal11_13
open MeasureTheory

/-- Binder-trade wrapper `firstPass_11_13_final_route1_derivedInputs21` of the counted form `firstPass_11_13_final_route1`: the binders hMf, hmeasure are discharged by `lqgMeasureLocality_derived` and `lqgMassInnerMeasurable_derived'`, both in `Phase2/CircleAverageLocalityLinkDerived.lean`; the conclusion is that of `firstPass_11_13_final_route1_derivedInputs20`. No binder is added. -/
theorem firstPass_11_13_final_route1_derivedInputs21
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanon : LQGCanonicalDecodersExistStmt.{0})
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK0 : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferK0Stmt)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final_route1_derivedInputs14 hAx hN2 hLoc
    hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCC) hE)
    hExists hDG hCC hE hfr hComp (HarmonicBalls.lqgMassInnerMeasurable_derived'.{0}) (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived.{0} hFA) hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1
    (HarmonicBalls.weylShiftedMassMeasurable_derived) hCal hK0 (HarmonicBalls.lqgMeasureLocality_derived.{0})

end HarmonicBalls.FirstPassS11iFinal11_13

