import HarmonicBalls.FirstPass.Phase2.DerivedInputs15
import HarmonicBalls.FirstPass.Phase2.DerivedInputs3
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9
import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived

/-! Binder-hygiene wrappers.
Each wrapper `<counted>_derivedInputs16` has the statement of `<counted>_derivedInputs15` minus the binder
`hDsm : SmallMetricDiameterLargeMassStmt` (HB result 11.9, Proposition 11.9, `prop:mass-diam-gen`;
`Draft/Section11.lean:201`). That binder is supplied by `HarmonicBalls.Closure.closure_11_9_derivedInputs3`
(`FirstPass/Phase2/DerivedInputs3.lean:32`): its binders `hCM` and `hMass` are discharged by the binder-free
`cameronMartinGFFMutualAbsCont_derived` and `lqgMassFunctionalMeasurable_derived`, and its other binders are
binders of the wrapper. No binder is added. Counted wrappers whose remaining binders do not allow this
discharge are not listed. Originals are unchanged. -/

universe u

open MeasureTheory

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Filter Topology Set Metric

/-- Binder-hygiene wrapper `closure_11_11_canonical_of_11_13_universe0_derivedInputs16` of the counted form `closure_11_11_canonical_of_11_13_universe0`: the binder `hDsm : SmallMetricDiameterLargeMassStmt` (HB result 11.9, `Draft/Section11.lean:201`) is removed and supplied by `HarmonicBalls.Closure.closure_11_9_derivedInputs3` (`FirstPass/Phase2/DerivedInputs3.lean:32`) with `hCM` and `hMass` from the binder-free `cameronMartinGFFMutualAbsCont_derived` and `lqgMassFunctionalMeasurable_derived`, and the other binders from the wrapper itself. The statement is that of `closure_11_11_canonical_of_11_13_universe0_derivedInputs15` minus `hDsm`; no binder is added. -/
theorem closure_11_11_canonical_of_11_13_universe0_derivedInputs16
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_11_11_canonical_of_11_13_universe0_derivedInputs14 hDG hE hL1 hE1
    hE3 hAx hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    hProf hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift hFD hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs16` of the counted form `closure_11_11_paperExponent_of_11_13_universe0`: the binder `hDsm : SmallMetricDiameterLargeMassStmt` (HB result 11.9, `Draft/Section11.lean:201`) is removed and supplied by `HarmonicBalls.Closure.closure_11_9_derivedInputs3` (`FirstPass/Phase2/DerivedInputs3.lean:32`) with `hCM` and `hMass` from the binder-free `cameronMartinGFFMutualAbsCont_derived` and `lqgMassFunctionalMeasurable_derived`, and the other binders from the wrapper itself. The statement is that of `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs15` minus `hDsm`; no binder is added. -/
theorem closure_11_11_paperExponent_of_11_13_universe0_derivedInputs16
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_11_11_paperExponent_of_11_13_universe0_derivedInputs14 _hDim hDG
    hE hL1 hE1 hE3 hAx hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    hProf hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift hFD hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_1_2_canonical_of_11_13_universe0_derivedInputs16` of the counted form `closure_1_2_canonical_of_11_13_universe0`: the binder `hDsm : SmallMetricDiameterLargeMassStmt` (HB result 11.9, `Draft/Section11.lean:201`) is removed and supplied by `HarmonicBalls.Closure.closure_11_9_derivedInputs3` (`FirstPass/Phase2/DerivedInputs3.lean:32`) with `hCM` and `hMass` from the binder-free `cameronMartinGFFMutualAbsCont_derived` and `lqgMassFunctionalMeasurable_derived`, and the other binders from the wrapper itself. The statement is that of `closure_1_2_canonical_of_11_13_universe0_derivedInputs15` minus `hDsm`; no binder is added. -/
theorem closure_1_2_canonical_of_11_13_universe0_derivedInputs16
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{0})
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_canonical_of_11_13_universe0_derivedInputs14 hDG hAff hE hL1
    hE1 hE3 hCamp hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    hProf hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift hFD hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs16` of the counted form `closure_1_2_faithful_canonical_of_11_13_universe0`: the binder `hDsm : SmallMetricDiameterLargeMassStmt` (HB result 11.9, `Draft/Section11.lean:201`) is removed and supplied by `HarmonicBalls.Closure.closure_11_9_derivedInputs3` (`FirstPass/Phase2/DerivedInputs3.lean:32`) with `hCM` and `hMass` from the binder-free `cameronMartinGFFMutualAbsCont_derived` and `lqgMassFunctionalMeasurable_derived`, and the other binders from the wrapper itself. The statement is that of `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs15` minus `hDsm`; no binder is added. -/
theorem closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs16
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{0})
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs14 hDG hAff
    hE hL1 hE1 hE3 hCamp hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    hProf hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift hFD hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs16` of the counted form `closure_1_2_paperExponent_of_11_13_universe0`: the binder `hDsm : SmallMetricDiameterLargeMassStmt` (HB result 11.9, `Draft/Section11.lean:201`) is removed and supplied by `HarmonicBalls.Closure.closure_11_9_derivedInputs3` (`FirstPass/Phase2/DerivedInputs3.lean:32`) with `hCM` and `hMass` from the binder-free `cameronMartinGFFMutualAbsCont_derived` and `lqgMassFunctionalMeasurable_derived`, and the other binders from the wrapper itself. The statement is that of `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs15` minus `hDsm`; no binder is added. -/
theorem closure_1_2_paperExponent_of_11_13_universe0_derivedInputs16
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{0})
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13_universe0_derivedInputs14 _hDim hDG
    hAff hE hL1 hE1 hE3 hCamp hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    hProf hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift hFD hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Filter Topology Set Metric

/-- Binder-hygiene wrapper `firstPass_11_11_faithful_universe0_derivedInputs16` of the counted form `firstPass_11_11_faithful_universe0`: the binder `hDsm : SmallMetricDiameterLargeMassStmt` (HB result 11.9, `Draft/Section11.lean:201`) is removed and supplied by `HarmonicBalls.Closure.closure_11_9_derivedInputs3` (`FirstPass/Phase2/DerivedInputs3.lean:32`) with `hCM` and `hMass` from the binder-free `cameronMartinGFFMutualAbsCont_derived` and `lqgMassFunctionalMeasurable_derived`, and the other binders from the wrapper itself. The statement is that of `firstPass_11_11_faithful_universe0_derivedInputs15` minus `hDsm`; no binder is added. -/
theorem firstPass_11_11_faithful_universe0_derivedInputs16
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.firstPass_11_11_faithful_universe0_derivedInputs14 hDG hE hL1 hE1 hE3 hAx
    hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    hProf hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift hFD hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `firstPass_1_2_faithful_universe0_derivedInputs16` of the counted form `firstPass_1_2_faithful_universe0`: the binder `hDsm : SmallMetricDiameterLargeMassStmt` (HB result 11.9, `Draft/Section11.lean:201`) is removed and supplied by `HarmonicBalls.Closure.closure_11_9_derivedInputs3` (`FirstPass/Phase2/DerivedInputs3.lean:32`) with `hCM` and `hMass` from the binder-free `cameronMartinGFFMutualAbsCont_derived` and `lqgMassFunctionalMeasurable_derived`, and the other binders from the wrapper itself. The statement is that of `firstPass_1_2_faithful_universe0_derivedInputs15` minus `hDsm`; no binder is added. -/
theorem firstPass_1_2_faithful_universe0_derivedInputs16
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{0})
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.firstPass_1_2_faithful_universe0_derivedInputs14 hDG hE hL1 hE1 hE3 hCamp
    hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    hProf hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift hFD hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.FirstPassS11iFinal11_13Close
open MeasureTheory Metric Set Filter Topology
open HarmonicBalls.FirstPassS11iFinal11_13

/-- Binder-hygiene wrapper `firstPass_11_13_closed_derivedInputs16` of the counted form `firstPass_11_13_closed`: the binder `hDsm : SmallMetricDiameterLargeMassStmt` (HB result 11.9, `Draft/Section11.lean:201`) is removed and supplied by `HarmonicBalls.Closure.closure_11_9_derivedInputs3` (`FirstPass/Phase2/DerivedInputs3.lean:32`) with `hCM` and `hMass` from the binder-free `cameronMartinGFFMutualAbsCont_derived` and `lqgMassFunctionalMeasurable_derived`, and the other binders from the wrapper itself. The statement is that of `firstPass_11_13_closed_derivedInputs15` minus `hDsm`; no binder is added. -/
theorem firstPass_11_13_closed_derivedInputs16
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13Close.firstPass_11_13_closed_derivedInputs14 hAx hN2 hLoc
    hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hDG hCCα hE hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1
    hRootCont hProf hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift hFD hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.FirstPassS11iFinal11_13Close

