import HarmonicBalls.FirstPass.Phase2.DerivedInputs10
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! Binder-hygiene wrappers, round 14 (fp-phase2-derived-inputs-14-weylscaling, worker z6).
Each wrapper `<counted>_derivedInputs10` (Phase2/DerivedInputs10.lean) that has the binder `hμW`, the universal
form of `LQGMeasureWeylScaling`, gets a wrapper `<counted>_derivedInputs14` with the same statement minus that
binder. The binder is supplied by the binder-free `HarmonicBalls.Section6.lqgMeasureWeylScaling`
(Proofs/Sec6/LQGWeylScaling.lean:124), whose type is the binder's type at every universe.
Originals are unchanged. Conclusions are unchanged and no other binder is removed. -/

universe u

namespace HarmonicBalls.Closure
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_11_11_canonical_derivedInputs14` of the counted form `closure_11_11_canonical` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_11_11_canonical_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_11_11_canonical_derivedInputs14
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_11_canonical_derivedInputs10 hDG hCC hE hL1 hE1 hE3 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hfr hComp hMf hDiam hMk
    hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hId hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_11_11_canonical_of_11_13_universe0_derivedInputs14` of the counted form `closure_11_11_canonical_of_11_13_universe0` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_11_11_canonical_of_11_13_universe0_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_11_11_canonical_of_11_13_universe0_derivedInputs14
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
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_11_11_canonical_of_11_13_universe0_derivedInputs10 hDG hE hL1 hE1
    hE3 hAx hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanonM hNonat hExists hCCα hfr
    hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf hWCont
    hA10 hDsm hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology

/-- Binder-hygiene wrapper `closure_11_11_paperExponent_derivedInputs14` of the counted form `closure_11_11_paperExponent` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_11_11_paperExponent_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_11_11_paperExponent_derivedInputs14
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_11_paperExponent_derivedInputs10 _hDim hDG hCC hE hL1 hE1 hE3
    hAx hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hfr hComp hMf
    hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hId hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Metric Set Filter Topology

/-- Binder-hygiene wrapper `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs14` of the counted form `closure_11_11_paperExponent_of_11_13_universe0` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_11_11_paperExponent_of_11_13_universe0_derivedInputs14
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
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_11_11_paperExponent_of_11_13_universe0_derivedInputs10 _hDim hDG
    hE hL1 hE1 hE3 hAx hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanonM hNonat hExists
    hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf
    hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory

/-- Binder-hygiene wrapper `closure_11_12_derivedInputs14` of the counted form `closure_11_12` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_11_12_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_11_12_derivedInputs14
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_12Stmt.{u} :=
    HarmonicBalls.Closure.closure_11_12_derivedInputs10 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hDG hCC hE hfr hComp hMf
    hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_11_12_clean_derivedInputs14` of the counted form `closure_11_12_clean` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_11_12_clean_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_11_12_clean_derivedInputs14
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_12CleanStmt.{u} :=
    HarmonicBalls.Closure.closure_11_12_clean_derivedInputs10 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hDG hCC hE hfr hComp hMf
    hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory

/-- Binder-hygiene wrapper `closure_11_13_canonical_derivedInputs14` of the counted form `closure_11_13_canonical` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_11_13_canonical_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_11_13_canonical_derivedInputs14
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_13_canonical_derivedInputs10 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hDG hCC hE hfr hComp hMf
    hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hId hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology

/-- Binder-hygiene wrapper `closure_11_13_paperExponent_derivedInputs14` of the counted form `closure_11_13_paperExponent` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_11_13_paperExponent_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_11_13_paperExponent_derivedInputs14
    (_hDim : WholePlaneLQGGraphDimension)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_13_paperExponent_derivedInputs10 _hDim hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hDG hCC hE hfr hComp hMf
    hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hId hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure

/-- Binder-hygiene wrapper `closure_1_2_canonical_derivedInputs14` of the counted form `closure_1_2_canonical` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_1_2_canonical_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_1_2_canonical_derivedInputs14
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyCanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_1_2_canonical_derivedInputs10 hDG hAff hCC hE hL1 hE1 hE3 hCamp
    hDec hCM hAx hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling hCanon hNonat hExists hfr hComp
    hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hId hTor hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_1_2_canonical_of_11_13_universe0_derivedInputs14` of the counted form `closure_1_2_canonical_of_11_13_universe0` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_1_2_canonical_of_11_13_universe0_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_1_2_canonical_of_11_13_universe0_derivedInputs14
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
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_canonical_of_11_13_universe0_derivedInputs10 hDG hAff hE hL1
    hE1 hE3 hCamp hDec hCM hAx hTor hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanonM
    hNonat hExists hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1
    hRootCont hProf hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure

/-- Binder-hygiene wrapper `closure_1_2_faithful_canonical_derivedInputs14` of the counted form `closure_1_2_faithful_canonical` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_1_2_faithful_canonical_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_1_2_faithful_canonical_derivedInputs14
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{u} :=
    HarmonicBalls.Closure.closure_1_2_faithful_canonical_derivedInputs10 hDG hAff hCC hE hL1 hE1 hE3
    hCamp hDec hCM hAx hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling hCanon hNonat hExists hfr
    hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hId hTor hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs14` of the counted form `closure_1_2_faithful_canonical_of_11_13_universe0` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs14
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
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs10 hDG hAff
    hE hL1 hE1 hE3 hCamp hDec hCM hAx hTor hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc
    hCanonM hNonat hExists hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM
    hFin hM1 hRootCont hProf hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology

/-- Binder-hygiene wrapper `closure_1_2_paperExponent_derivedInputs14` of the counted form `closure_1_2_paperExponent` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_1_2_paperExponent_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_1_2_paperExponent_derivedInputs14
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{u} :=
    HarmonicBalls.Closure.closure_1_2_paperExponent_derivedInputs10 _hDim hDG hAff hCC hE hL1 hE1
    hE3 hCamp hDec hCM hAx hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling hCanon hNonat hExists
    hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hId hTor hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Metric Set Filter Topology

/-- Binder-hygiene wrapper `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs14` of the counted form `closure_1_2_paperExponent_of_11_13_universe0` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem closure_1_2_paperExponent_of_11_13_universe0_derivedInputs14
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
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13_universe0_derivedInputs10 _hDim hDG
    hAff hE hL1 hE1 hE3 hCamp hDec hCM hAx hTor hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling
    hLoc hCanonM hNonat hExists hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10
    hSupM hFin hM1 hRootCont hProf hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Binder-hygiene wrapper `firstPass_11_11_faithful_universe0_derivedInputs14` of the counted form `firstPass_11_11_faithful_universe0` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `firstPass_11_11_faithful_universe0_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem firstPass_11_11_faithful_universe0_derivedInputs14
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
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.firstPass_11_11_faithful_universe0_derivedInputs10 hDG hE hL1 hE1 hE3 hAx
    hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanonM hNonat hExists hCCα hfr hComp hMf
    hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf hWCont hA10 hDsm hK
    hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.S11m.Clean11_12
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `firstPass_11_12_clean_derivedInputs14` of the counted form `firstPass_11_12_clean` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `firstPass_11_12_clean_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem firstPass_11_12_clean_derivedInputs14
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    (hComp : WeylScalingCompositionFrozen.{u})
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    : CorrectedLemma11_12CleanStmt.{u} :=
    HarmonicBalls.S11m.Clean11_12.firstPass_11_12_clean_derivedInputs10 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hDG hCC hE hfr hmass
    hCMAbs hComp hDsm hMf hDiam hMk hholder

end HarmonicBalls.S11m.Clean11_12

namespace HarmonicBalls.S11m.Final11_12
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Binder-hygiene wrapper `firstPass_11_12_final_derivedInputs14` of the counted form `firstPass_11_12_final` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `firstPass_11_12_final_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem firstPass_11_12_final_derivedInputs14
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    (hComp : WeylScalingCompositionFrozen.{u})
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    : CorrectedLemma11_12Stmt.{u} :=
    HarmonicBalls.S11m.Final11_12.firstPass_11_12_final_derivedInputs10 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hDG hCC hE hfr hmass
    hCMAbs hComp hDsm hMf hDiam hMk hholder

end HarmonicBalls.S11m.Final11_12

namespace HarmonicBalls.FirstPassS11iFinal11_13
open MeasureTheory

/-- Binder-hygiene wrapper `firstPass_11_13_derivedInputs14` of the counted form `firstPass_11_13` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `firstPass_11_13_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem firstPass_11_13_derivedInputs14
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
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
    (hM2 : WeylShiftedMassMeasurableFrozen.{0})
    (_hBirk : BirkhoffPointwiseErgodic.{0})
    (_hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (_hProf : LQGMeasureOfProfileMeasurableFrozen.{0})
    (_hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (_hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_derivedInputs10 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanonM hNonat hExists hDG hCCα hE hfr hComp
    hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 _hBirk _hRootCont _hProf
    _hWCont _hA10 hCal hK hmeasure

end HarmonicBalls.FirstPassS11iFinal11_13

namespace HarmonicBalls.FirstPassS11iAssembly11_13
open MeasureTheory

/-- Binder-hygiene wrapper `firstPass_11_13_canonical_derivedInputs14` of the counted form `firstPass_11_13_canonical` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `firstPass_11_13_canonical_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem firstPass_11_13_canonical_derivedInputs14
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{u} :=
    HarmonicBalls.FirstPassS11iAssembly11_13.firstPass_11_13_canonical_derivedInputs10 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hDG hCC hE hfr hComp hMf
    hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hId hmeasure

end HarmonicBalls.FirstPassS11iAssembly11_13

namespace HarmonicBalls.FirstPassS11iFinal11_13Close
open MeasureTheory Metric Set Filter Topology
open HarmonicBalls.FirstPassS11iFinal11_13

/-- Binder-hygiene wrapper `firstPass_11_13_closed_derivedInputs14` of the counted form `firstPass_11_13_closed` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `firstPass_11_13_closed_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem firstPass_11_13_closed_derivedInputs14
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13Close.firstPass_11_13_closed_derivedInputs10 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanonM hNonat hExists hDG hCCα hE hfr hComp
    hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf hWCont hA10 hDsm
    hK hmeasure

end HarmonicBalls.FirstPassS11iFinal11_13Close

namespace HarmonicBalls.FirstPassS11iFinal11_13
open MeasureTheory

/-- Binder-hygiene wrapper `firstPass_11_13_final_derivedInputs14` of the counted form `firstPass_11_13_final` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `firstPass_11_13_final_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem firstPass_11_13_final_derivedInputs14
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanon : LQGCanonicalDecodersExistStmt.{0})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC0 : HarmonicBalls.FirstPassS11iStep8PhysExists.CoordChangeZeroStmt)
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
    (hM2 : WeylShiftedMassMeasurableFrozen.{0})
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hIns : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferStmt)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final_derivedInputs10 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hDG hCC0 hE hfr hComp
    hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hCal hIns hmeasure

/-- Binder-hygiene wrapper `firstPass_11_13_final_route1_derivedInputs14` of the counted form `firstPass_11_13_final_route1` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `firstPass_11_13_final_route1_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem firstPass_11_13_final_route1_derivedInputs14
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanon : LQGCanonicalDecodersExistStmt.{0})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
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
    (hM2 : WeylShiftedMassMeasurableFrozen.{0})
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK0 : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferK0Stmt)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final_route1_derivedInputs10 hAx hN2
    HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanon hNonat hExists hDG hCCα hE hfr hComp
    hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hM2 hCal hK0 hmeasure

end HarmonicBalls.FirstPassS11iFinal11_13

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `firstPass_1_2_faithful_universe0_derivedInputs14` of the counted form `firstPass_1_2_faithful_universe0` (fp-phase2-derived-inputs-14, worker z6): the binder `hμW` (the universal form of `LQGMeasureWeylScaling`, Proposed/LQG.lean) is removed and supplied by `HarmonicBalls.Section6.lqgMeasureWeylScaling` (Proofs/Sec6/LQGWeylScaling.lean:124, binder-free). The statement is that of `firstPass_1_2_faithful_universe0_derivedInputs10` minus `hμW`; no other binder and no conclusion is changed. -/
theorem firstPass_1_2_faithful_universe0_derivedInputs14
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
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.firstPass_1_2_faithful_universe0_derivedInputs10 hDG hE hL1 hE1 hE3 hCamp
    hDec hCM hAx hTor hN2 HarmonicBalls.Section6.lqgMeasureWeylScaling hLoc hCanonM hNonat hExists
    hCCα hfr hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf
    hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure
