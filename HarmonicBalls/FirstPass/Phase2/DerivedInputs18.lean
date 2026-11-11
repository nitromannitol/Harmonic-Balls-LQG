import HarmonicBalls.FirstPass.Phase2.DerivedInputs16
import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived
import HarmonicBalls.FirstPass.Phase2.PlaneDomainDerived
import HarmonicBalls.FirstPass.Phase2.WeylShiftedMassDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs11
import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9
import HarmonicBalls.FirstPass.S8c.BirkhoffDerived

/-! Binder-hygiene wrappers, round 18 (fp-audit-r1-close-and-di18, worker z6).
The 23 counted wrappers of the DI15 family (the 8 `_derivedInputs16` wrappers, and the 15 `_derivedInputs15`
wrappers without a DI16 version) are restated without every binder whose Prop has a binder-free derived theorem:
`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`,
`WeylShiftedMassMeasurableFrozen`, `WholePlaneGFFAffineInvariance`, `LQGMassFunctionalMeasurableFrozen`,
`CameronMartinGFFMutualAbsCont` and `BirkhoffPointwiseErgodic`. Each removed binder is replaced in the proof by
its derived theorem. No binder is added; the conclusions are unchanged. Originals are unchanged. -/

universe u

open MeasureTheory

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Filter Topology Set Metric

/-- Binder-hygiene wrapper `closure_11_11_canonical_of_11_13_universe0_derivedInputs18` of the counted form `closure_11_11_canonical_of_11_13_universe0` (fp-phase2-derived-inputs-18, worker z6): the binders `hE1`, `hFD`, `hProf` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`). The statement is that of `closure_11_11_canonical_of_11_13_universe0_derivedInputs16` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_11_11_canonical_of_11_13_universe0_derivedInputs18
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
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
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_11_11_canonical_of_11_13_universe0_derivedInputs14 hDG hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    hE3 hAx hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs18` of the counted form `closure_11_11_paperExponent_of_11_13_universe0` (fp-phase2-derived-inputs-18, worker z6): the binders `hE1`, `hFD`, `hProf` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`). The statement is that of `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs16` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_11_11_paperExponent_of_11_13_universe0_derivedInputs18
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
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
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_11_11_paperExponent_of_11_13_universe0_derivedInputs14 _hDim hDG
    hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hAx hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_1_2_canonical_of_11_13_universe0_derivedInputs18` of the counted form `closure_1_2_canonical_of_11_13_universe0` (fp-phase2-derived-inputs-18, worker z6): the binders `hAff`, `hE1`, `hFD`, `hProf` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WholePlaneGFFAffineInvariance`). The statement is that of `closure_1_2_canonical_of_11_13_universe0_derivedInputs16` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_1_2_canonical_of_11_13_universe0_derivedInputs18
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
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
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyCanonicalStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_canonical_of_11_13_universe0_derivedInputs14 hDG (HarmonicBalls.WholePlaneGFFAffineInvariance_derived) hE hL1
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hCamp hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs18` of the counted form `closure_1_2_faithful_canonical_of_11_13_universe0` (fp-phase2-derived-inputs-18, worker z6): the binders `hAff`, `hE1`, `hFD`, `hProf` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WholePlaneGFFAffineInvariance`). The statement is that of `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs16` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs18
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
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
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs14 hDG (HarmonicBalls.WholePlaneGFFAffineInvariance_derived)
    hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hCamp hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs18` of the counted form `closure_1_2_paperExponent_of_11_13_universe0` (fp-phase2-derived-inputs-18, worker z6): the binders `hAff`, `hE1`, `hFD`, `hProf` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WholePlaneGFFAffineInvariance`). The statement is that of `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs16` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_1_2_paperExponent_of_11_13_universe0_derivedInputs18
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
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
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13_universe0_derivedInputs14 _hDim hDG
    (HarmonicBalls.WholePlaneGFFAffineInvariance_derived) hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hCamp hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Filter Topology Set Metric

/-- Binder-hygiene wrapper `firstPass_11_11_faithful_universe0_derivedInputs18` of the counted form `firstPass_11_11_faithful_universe0` (fp-phase2-derived-inputs-18, worker z6): the binders `hE1`, `hFD`, `hProf` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`). The statement is that of `firstPass_11_11_faithful_universe0_derivedInputs16` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem firstPass_11_11_faithful_universe0_derivedInputs18
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
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
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{0} :=
    HarmonicBalls.Closure.firstPass_11_11_faithful_universe0_derivedInputs14 hDG hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hAx
    hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.FirstPassS11iFinal11_13Close
open MeasureTheory Metric Set Filter Topology
open HarmonicBalls.FirstPassS11iFinal11_13

/-- Binder-hygiene wrapper `firstPass_11_13_closed_derivedInputs18` of the counted form `firstPass_11_13_closed` (fp-phase2-derived-inputs-18, worker z6): the binders `hFD`, `hProf` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`). The statement is that of `firstPass_11_13_closed_derivedInputs16` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem firstPass_11_13_closed_derivedInputs18
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
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hCMT : CameronMartinEventTransferFrozen.{0})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
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
    hExists hDG hCCα hE hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1
    hRootCont (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.FirstPassS11iFinal11_13Close

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `firstPass_1_2_faithful_universe0_derivedInputs18` of the counted form `firstPass_1_2_faithful_universe0` (fp-phase2-derived-inputs-18, worker z6): the binders `hE1`, `hFD`, `hProf` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`). The statement is that of `firstPass_1_2_faithful_universe0_derivedInputs16` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem firstPass_1_2_faithful_universe0_derivedInputs18
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
    (hComp : WeylScalingCompositionFrozen.{0})
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
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
    (hWCont : WeylMetricCompositionContinuousOuterFrozen)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
    HarmonicBalls.Closure.firstPass_1_2_faithful_universe0_derivedInputs14 hDG hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hCamp
    hDec hCM hAx hTor hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hCCα hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 hRootCont
    (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hWCont hA10 (HarmonicBalls.Closure.closure_11_9_derivedInputs3 HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived hComp hfr HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hAx hDC hCMT hPos10 hSupM hFin hM1 hmeasure) hK hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_11_11_canonical_derivedInputs18` of the counted form `closure_11_11_canonical` (fp-phase2-derived-inputs-18, worker z6): the binders `hE1`, `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`). The statement is that of `closure_11_11_canonical_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_11_11_canonical_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
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
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_11_canonical_derivedInputs14 hDG hCC hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hAx hN2
    hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_univ hCC) hE)
    hExists hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId
    hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology

/-- Binder-hygiene wrapper `closure_11_11_paperExponent_derivedInputs18` of the counted form `closure_11_11_paperExponent` (fp-phase2-derived-inputs-18, worker z6): the binders `hE1`, `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`). The statement is that of `closure_11_11_paperExponent_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_11_11_paperExponent_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
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
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNotMetricBallCanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_11_paperExponent_derivedInputs14 _hDim hDG hCC hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3
    hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_univ hCC) hE)
    hExists hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId
    hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory

/-- Binder-hygiene wrapper `closure_11_12_derivedInputs18` of the counted form `closure_11_12` (fp-phase2-derived-inputs-18, worker z6): the binders `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`). The statement is that of `closure_11_12_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_11_12_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_12Stmt.{u} :=
    HarmonicBalls.Closure.closure_11_12_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr hComp hMf
    hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `closure_11_12_clean_derivedInputs18` of the counted form `closure_11_12_clean` (fp-phase2-derived-inputs-18, worker z6): the binders `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`). The statement is that of `closure_11_12_clean_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_11_12_clean_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_12CleanStmt.{u} :=
    HarmonicBalls.Closure.closure_11_12_clean_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr hComp hMf
    hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory

/-- Binder-hygiene wrapper `closure_11_13_canonical_derivedInputs18` of the counted form `closure_11_13_canonical` (fp-phase2-derived-inputs-18, worker z6): the binders `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`). The statement is that of `closure_11_13_canonical_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_11_13_canonical_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
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
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_13_canonical_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr hComp hMf
    hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology

/-- Binder-hygiene wrapper `closure_11_13_paperExponent_derivedInputs18` of the counted form `closure_11_13_paperExponent` (fp-phase2-derived-inputs-18, worker z6): the binders `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`). The statement is that of `closure_11_13_paperExponent_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_11_13_paperExponent_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
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
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_11_13_paperExponent_derivedInputs14 _hDim hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr hComp hMf
    hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure

/-- Binder-hygiene wrapper `closure_1_2_canonical_derivedInputs18` of the counted form `closure_1_2_canonical` (fp-phase2-derived-inputs-18, worker z6): the binders `hAff`, `hE1`, `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`, `WholePlaneGFFAffineInvariance`). The statement is that of `closure_1_2_canonical_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_1_2_canonical_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
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
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyCanonicalStmt.{u} :=
    HarmonicBalls.Closure.closure_1_2_canonical_derivedInputs14 hDG (HarmonicBalls.WholePlaneGFFAffineInvariance_derived) hCC hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3 hCamp
    hDec hCM hAx hN2 hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_univ hCC) hE)
    hExists hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId hTor
    hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure

/-- Binder-hygiene wrapper `closure_1_2_faithful_canonical_derivedInputs18` of the counted form `closure_1_2_faithful_canonical` (fp-phase2-derived-inputs-18, worker z6): the binders `hAff`, `hE1`, `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`, `WholePlaneGFFAffineInvariance`). The statement is that of `closure_1_2_faithful_canonical_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_1_2_faithful_canonical_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
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
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{u} :=
    HarmonicBalls.Closure.closure_1_2_faithful_canonical_derivedInputs14 hDG (HarmonicBalls.WholePlaneGFFAffineInvariance_derived) hCC hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) hE3
    hCamp hDec hCM hAx hN2 hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_univ hCC) hE)
    hExists hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId hTor
    hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology

/-- Binder-hygiene wrapper `closure_1_2_paperExponent_derivedInputs18` of the counted form `closure_1_2_paperExponent` (fp-phase2-derived-inputs-18, worker z6): the binders `hAff`, `hE1`, `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`, `WholePlaneGFFAffineInvariance`). The statement is that of `closure_1_2_paperExponent_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem closure_1_2_paperExponent_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
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
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : HarmonicBallNoveltyFaithfulStmt.{u} :=
    HarmonicBalls.Closure.closure_1_2_paperExponent_derivedInputs14 _hDim hDG (HarmonicBalls.WholePlaneGFFAffineInvariance_derived) hCC hE hL1 (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    hE3 hCamp hDec hCM hAx hN2 hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_univ hCC) hE)
    hExists hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId hTor
    hmeasure

end HarmonicBalls.Closure

namespace HarmonicBalls.S11m.Clean11_12
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper `firstPass_11_12_clean_derivedInputs18` of the counted form `firstPass_11_12_clean` (fp-phase2-derived-inputs-18, worker z6): the binders `hmass`, `hCMAbs` are removed and supplied by binder-free derived theorems for their Props (`CameronMartinGFFMutualAbsCont`, `LQGMassFunctionalMeasurableFrozen`). The statement is that of `firstPass_11_12_clean_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem firstPass_11_12_clean_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    : CorrectedLemma11_12CleanStmt.{u} :=
    HarmonicBalls.S11m.Clean11_12.firstPass_11_12_clean_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr (HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived) (HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived)
    hComp hDsm hMf hDiam hMk hholder

end HarmonicBalls.S11m.Clean11_12

namespace HarmonicBalls.S11m.Final11_12
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Binder-hygiene wrapper `firstPass_11_12_final_derivedInputs18` of the counted form `firstPass_11_12_final` (fp-phase2-derived-inputs-18, worker z6): the binders `hmass`, `hCMAbs` are removed and supplied by binder-free derived theorems for their Props (`CameronMartinGFFMutualAbsCont`, `LQGMassFunctionalMeasurableFrozen`). The statement is that of `firstPass_11_12_final_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem firstPass_11_12_final_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    : CorrectedLemma11_12Stmt.{u} :=
    HarmonicBalls.S11m.Final11_12.firstPass_11_12_final_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr (HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived) (HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived)
    hComp hDsm hMf hDiam hMk hholder

end HarmonicBalls.S11m.Final11_12

namespace HarmonicBalls.FirstPassS11iFinal11_13
open MeasureTheory

/-- Binder-hygiene wrapper `firstPass_11_13_derivedInputs18` of the counted form `firstPass_11_13` (fp-phase2-derived-inputs-18, worker z6): the binders `hFD`, `hM2`, `_hBirk`, `_hProf` are removed and supplied by binder-free derived theorems for their Props (`BirkhoffPointwiseErgodic`, `LQGMeasureOfProfileMeasurableFrozen`, `PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`). The statement is that of `firstPass_11_13_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem firstPass_11_13_derivedInputs18
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
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_derivedInputs14 hAx hN2 hLoc hCanonM
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hDG hCCα hE hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1
    (HarmonicBalls.weylShiftedMassMeasurable_derived) (HarmonicBalls.birkhoffPointwiseErgodic_derived) _hRootCont (HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) _hWCont _hA10 hCal hK hmeasure

end HarmonicBalls.FirstPassS11iFinal11_13

namespace HarmonicBalls.FirstPassS11iAssembly11_13
open MeasureTheory

/-- Binder-hygiene wrapper `firstPass_11_13_canonical_derivedInputs18` of the counted form `firstPass_11_13_canonical` (fp-phase2-derived-inputs-18, worker z6): the binders `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`). The statement is that of `firstPass_11_13_canonical_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem firstPass_11_13_canonical_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
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
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{u} :=
    HarmonicBalls.FirstPassS11iAssembly11_13.firstPass_11_13_canonical_derivedInputs14 hAx hN2 hLoc
    hCanon (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG hCC hE) hExists hDG hCC hE hfr hComp
    hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1 (HarmonicBalls.weylShiftedMassMeasurable_derived) hId hmeasure

end HarmonicBalls.FirstPassS11iAssembly11_13

namespace HarmonicBalls.FirstPassS11iFinal11_13
open MeasureTheory

/-- Binder-hygiene wrapper `firstPass_11_13_final_derivedInputs18` of the counted form `firstPass_11_13_final` (fp-phase2-derived-inputs-18, worker z6): the binders `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`). The statement is that of `firstPass_11_13_final_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem firstPass_11_13_final_derivedInputs18
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
    (hMf : LQGMassInnerMeasurableFrozen.{0})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{0})
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
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final_derivedInputs14 hAx hN2 hLoc hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_zeroStmt hCC0) hE)
    hExists hDG hCC0 hE hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1
    (HarmonicBalls.weylShiftedMassMeasurable_derived) hCal hIns hmeasure

end HarmonicBalls.FirstPassS11iFinal11_13

namespace HarmonicBalls.FirstPassS11iFinal11_13
open MeasureTheory

/-- Binder-hygiene wrapper `firstPass_11_13_final_route1_derivedInputs18` of the counted form `firstPass_11_13_final_route1` (fp-phase2-derived-inputs-18, worker z6): the binders `hFD`, `hM2` are removed and supplied by binder-free derived theorems for their Props (`PlaneDomainMinusConvexCompactPreconnectedFrozen`, `WeylShiftedMassMeasurableFrozen`). The statement is that of `firstPass_11_13_final_route1_derivedInputs15` minus these binders; no binder is added and the conclusion is unchanged. -/
theorem firstPass_11_13_final_route1_derivedInputs18
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanon : LQGCanonicalDecodersExistStmt.{0})
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
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hCMT : CameronMartinEventTransferFrozen.{0})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK0 : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferK0Stmt)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type 0) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
    HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final_route1_derivedInputs14 hAx hN2 hLoc
    hCanon
    (HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (HarmonicBalls.coordChangeZero_of_alpha0Stmt hCCα) hE)
    hExists hDG hCCα hE hfr hComp hMf hDiam hMk hholder hShift (HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived) hDC hCMT hPos10 hSupM hFin hM1
    (HarmonicBalls.weylShiftedMassMeasurable_derived) hCal hK0 hmeasure

end HarmonicBalls.FirstPassS11iFinal11_13

