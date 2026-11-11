import HarmonicBalls.FirstPass.Phase2.DerivedInputs5

/-! Binder-hygiene wrappers (fp-phase2-binder-hygiene, z6). The universe-0 counted forms listed here lose the
binders hCC, hW, hN, which are derived from hCCα, hμW, hNonat by the proved lemmas of DerivedInputs4
(`coordChange_of_alpha0`, `weylScaling_at_zero`, `nonatomic_reorder`). Originals are unchanged. -/

namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper of `closure_1_2_canonical_of_11_13_universe0` (fp-phase2-binder-hygiene): the binders hCC, hW, hN are removed and supplied by `coordChange_of_alpha0 hCCα`, `weylScaling_at_zero hμW`, `nonatomic_reorder hNonat` (FirstPass/Phase2/DerivedInputs4.lean, proved at universe 0). The statement is unchanged; no conclusion is weakened. -/
theorem closure_1_2_canonical_of_11_13_universe0_derivedInputs7
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
    (hLen : LQGMetricLengthUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
  HarmonicBalls.Closure.closure_1_2_canonical_of_11_13_universe0 hDG hAff (HarmonicBalls.DerivedInputs4.coordChange_of_alpha0 hCCα) (HarmonicBalls.DerivedInputs4.weylScaling_at_zero hμW) hE (HarmonicBalls.DerivedInputs4.nonatomic_reorder hNonat) hL1 hE1 hE3 hCamp hDec hCM hAx hTor hLen hN2 hμW hLoc hCanonM hNonat hExists hCCα hfr hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper of `closure_1_2_faithful_canonical_of_11_13_universe0` (fp-phase2-binder-hygiene): the binders hCC, hW, hN are removed and supplied by `coordChange_of_alpha0 hCCα`, `weylScaling_at_zero hμW`, `nonatomic_reorder hNonat` (FirstPass/Phase2/DerivedInputs4.lean, proved at universe 0). The statement is unchanged; no conclusion is weakened. -/
theorem closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs7
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
    (hLen : LQGMetricLengthUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
  HarmonicBalls.Closure.closure_1_2_faithful_canonical_of_11_13_universe0 hDG hAff (HarmonicBalls.DerivedInputs4.coordChange_of_alpha0 hCCα) (HarmonicBalls.DerivedInputs4.weylScaling_at_zero hμW) hE (HarmonicBalls.DerivedInputs4.nonatomic_reorder hNonat) hL1 hE1 hE3 hCamp hDec hCM hAx hTor hLen hN2 hμW hLoc hCanonM hNonat hExists hCCα hfr hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-hygiene wrapper of `firstPass_1_2_faithful_universe0` (fp-phase2-binder-hygiene): the binders hCC, hW, hN are removed and supplied by `coordChange_of_alpha0 hCCα`, `weylScaling_at_zero hμW`, `nonatomic_reorder hNonat` (FirstPass/Phase2/DerivedInputs4.lean, proved at universe 0). The statement is unchanged; no conclusion is weakened. -/
theorem firstPass_1_2_faithful_universe0_derivedInputs7
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
    (hLen : LQGMetricLengthUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
  HarmonicBalls.Closure.firstPass_1_2_faithful_universe0 hDG (HarmonicBalls.DerivedInputs4.coordChange_of_alpha0 hCCα) (HarmonicBalls.DerivedInputs4.weylScaling_at_zero hμW) hE (HarmonicBalls.DerivedInputs4.nonatomic_reorder hNonat) hL1 hE1 hE3 hCamp hDec hCM hAx hTor hLen hN2 hμW hLoc hCanonM hNonat hExists hCCα hfr hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Metric Set Filter Topology

/-- Binder-hygiene wrapper of `closure_1_2_paperExponent_of_11_13_universe0` (fp-phase2-binder-hygiene): the binders hCC, hW, hN are removed and supplied by `coordChange_of_alpha0 hCCα`, `weylScaling_at_zero hμW`, `nonatomic_reorder hNonat` (FirstPass/Phase2/DerivedInputs4.lean, proved at universe 0). The statement is unchanged; no conclusion is weakened. -/
theorem closure_1_2_paperExponent_of_11_13_universe0_derivedInputs7
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
    (hLen : LQGMetricLengthUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{0})
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{0})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
  HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13_universe0 _hDim hDG hAff (HarmonicBalls.DerivedInputs4.coordChange_of_alpha0 hCCα) (HarmonicBalls.DerivedInputs4.weylScaling_at_zero hμW) hE (HarmonicBalls.DerivedInputs4.nonatomic_reorder hNonat) hL1 hE1 hE3 hCamp hDec hCM hAx hTor hLen hN2 hμW hLoc hCanonM hNonat hExists hCCα hfr hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Metric Set Filter Topology

/-- Binder-hygiene wrapper of `closure_11_11_paperExponent_of_11_13_universe0` (fp-phase2-binder-hygiene): the binders hCC, hW, hN are removed and supplied by `coordChange_of_alpha0 hCCα`, `weylScaling_at_zero hμW`, `nonatomic_reorder hNonat` (FirstPass/Phase2/DerivedInputs4.lean, proved at universe 0). The statement is unchanged; no conclusion is weakened. -/
theorem closure_11_11_paperExponent_of_11_13_universe0_derivedInputs7
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
  HarmonicBalls.Closure.closure_11_11_paperExponent_of_11_13_universe0 _hDim hDG (HarmonicBalls.DerivedInputs4.coordChange_of_alpha0 hCCα) hE (HarmonicBalls.DerivedInputs4.weylScaling_at_zero hμW) (HarmonicBalls.DerivedInputs4.nonatomic_reorder hNonat) hL1 hE1 hE3 hAx hLen hN2 hμW hLoc hCanonM hNonat hExists hCCα hfr hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Binder-hygiene wrapper of `closure_11_11_canonical_of_11_13_universe0` (fp-phase2-binder-hygiene): the binders hCC, hW, hN are removed and supplied by `coordChange_of_alpha0 hCCα`, `weylScaling_at_zero hμW`, `nonatomic_reorder hNonat` (FirstPass/Phase2/DerivedInputs4.lean, proved at universe 0). The statement is unchanged; no conclusion is weakened. -/
theorem closure_11_11_canonical_of_11_13_universe0_derivedInputs7
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
  HarmonicBalls.Closure.closure_11_11_canonical_of_11_13_universe0 hDG (HarmonicBalls.DerivedInputs4.coordChange_of_alpha0 hCCα) hE (HarmonicBalls.DerivedInputs4.weylScaling_at_zero hμW) (HarmonicBalls.DerivedInputs4.nonatomic_reorder hNonat) hL1 hE1 hE3 hAx hLen hN2 hμW hLoc hCanonM hNonat hExists hCCα hfr hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Binder-hygiene wrapper of `firstPass_11_11_faithful_universe0` (fp-phase2-binder-hygiene): the binders hCC, hW, hN are removed and supplied by `coordChange_of_alpha0 hCCα`, `weylScaling_at_zero hμW`, `nonatomic_reorder hNonat` (FirstPass/Phase2/DerivedInputs4.lean, proved at universe 0). The statement is unchanged; no conclusion is weakened. -/
theorem firstPass_11_11_faithful_universe0_derivedInputs7
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
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
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{0})
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
  HarmonicBalls.Closure.firstPass_11_11_faithful_universe0 hDG (HarmonicBalls.DerivedInputs4.coordChange_of_alpha0 hCCα) hE (HarmonicBalls.DerivedInputs4.weylScaling_at_zero hμW) (HarmonicBalls.DerivedInputs4.nonatomic_reorder hNonat) hL1 hE1 hE3 hAx hLen hN2 hμW hLoc hCanonM hNonat hExists hCCα hfr hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hSupM hFin hM1 hRootCont hProf hWCont hA10 hDsm hK hmeasure

end HarmonicBalls.Closure
