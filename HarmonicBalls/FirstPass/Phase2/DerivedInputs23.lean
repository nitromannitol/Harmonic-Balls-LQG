import HarmonicBalls.FirstPass.Phase2.DerivedInputs21
import HarmonicBalls.FirstPass.Phase2.DerivedInputs19
import HarmonicBalls.FirstPass.Phase2.WeylCompositionOuterDerived
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences

/-!
# Derived inputs, round 23 (worker z6, fp-audit-r2-binders)

Binder-trade wrappers (audit R2, items M12 and HB(B) binders) of the round-21 counted forms of Theorem 1.2,
Proposition 11.11 and Lemma 11.13, and of the round-19 form of Theorem 8.2. A binder is dropped only when the
wrapper supplies it from a binder it keeps or from a named lemma:
* `hDec` replaces the duplicate `hLoc` (same Prop, `LocalLQGDecoderCommonFrozen`);
* `_hWCont` is discharged by `weylMetricCompositionContinuousOuter_derived` (Phase2/WeylCompositionOuterDerived.lean);
* `hfull` (`LQGMeasureFullSupportStmt`) is discharged by `lqgMeasureFullSupportStmt_of_existence`
  (Proofs/Sec9/LQGExistenceConsequences.lean:46), whose section variables are `hDG`, `hCC` (at α₀ = 0), `hE`.
`GreenPotentialHolderStmt` (`hholder`) and `hDsm` are not discharged here (see COUNTED-MANIFEST.md). -/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.Closure

/-- Binder-trade wrapper `closure_1_2_canonical_of_11_13_universe0_derivedInputs23` of `closure_1_2_canonical_of_11_13_universe0_derivedInputs21` (fp-audit-r2-binders, worker z6): `hLoc` is discharged by `hDec`. The conclusion and the other binders are those of `closure_1_2_canonical_of_11_13_universe0_derivedInputs21`. -/
theorem closure_1_2_canonical_of_11_13_universe0_derivedInputs23
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNoveltyCanonicalStmt.{0} :=
  HarmonicBalls.Closure.closure_1_2_canonical_of_11_13_universe0_derivedInputs21 (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM) (hAx := hAx) (hTor := hTor) (hN2 := hN2) (hLoc := hDec) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hM1 := hM1) (hRootCont := hRootCont) (hA10 := hA10) (hK := hK)

/-- Binder-trade wrapper `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs23` of `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs21` (fp-audit-r2-binders, worker z6): `hLoc` is discharged by `hDec`. The conclusion and the other binders are those of `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs21`. -/
theorem closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs23
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
  HarmonicBalls.Closure.closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs21 (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM) (hAx := hAx) (hTor := hTor) (hN2 := hN2) (hLoc := hDec) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hM1 := hM1) (hRootCont := hRootCont) (hA10 := hA10) (hK := hK)

/-- Binder-trade wrapper `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs23` of `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs21` (fp-audit-r2-binders, worker z6): `hLoc` is discharged by `hDec`. The conclusion and the other binders are those of `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs21`. -/
theorem closure_1_2_paperExponent_of_11_13_universe0_derivedInputs23
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
  HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13_universe0_derivedInputs21 (_hDim := _hDim) (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM) (hAx := hAx) (hTor := hTor) (hN2 := hN2) (hLoc := hDec) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hM1 := hM1) (hRootCont := hRootCont) (hA10 := hA10) (hK := hK)

/-- Binder-trade wrapper `firstPass_1_2_faithful_universe0_derivedInputs23` of `firstPass_1_2_faithful_universe0_derivedInputs21` (fp-audit-r2-binders, worker z6): `hLoc` is discharged by `hDec`. The conclusion and the other binders are those of `firstPass_1_2_faithful_universe0_derivedInputs21`. -/
theorem firstPass_1_2_faithful_universe0_derivedInputs23
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
    (hPos10 : LQGMeasureSquarePositiveFrozen.{0})
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hM1 : WeylShiftedSupMeasurableFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : HarmonicBallNoveltyFaithfulStmt.{0} :=
  HarmonicBalls.Closure.firstPass_1_2_faithful_universe0_derivedInputs21 (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM) (hAx := hAx) (hTor := hTor) (hN2 := hN2) (hLoc := hDec) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hM1 := hM1) (hRootCont := hRootCont) (hA10 := hA10) (hK := hK)

end HarmonicBalls.Closure

namespace HarmonicBalls.FirstPassS11iFinal11_13

/-- Binder-trade wrapper `firstPass_11_13_derivedInputs23` of `firstPass_11_13_derivedInputs21` (fp-audit-r2-binders, worker z6): `_hWCont` is discharged by `weylMetricCompositionContinuousOuter_derived`. The conclusion and the other binders are those of `firstPass_11_13_derivedInputs21`. -/
theorem firstPass_11_13_derivedInputs23
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
    (_hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK : ∀ (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    : CorrectedLemma11_13CanonicalStmt.{0} :=
  HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_derivedInputs21 (hAx := hAx) (hN2 := hN2) (hLoc := hLoc) (hCanonM := hCanonM) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hM1 := hM1) (_hRootCont := _hRootCont) (_hWCont := HarmonicBalls.weylMetricCompositionContinuousOuter_derived) (_hA10 := _hA10) (hCal := hCal) (hK := hK)

end HarmonicBalls.FirstPassS11iFinal11_13

namespace HarmonicBalls

/-- Binder-trade wrapper `firstPass_8_2_S8d_noWeyl_derivedInputs23` of `firstPass_8_2_S8d_noWeyl_derivedInputs19` (fp-audit-r2-binders, worker z6): `hfull` is discharged by `lqgMeasureFullSupportStmt_of_existence` (Proofs/Sec9/LQGExistenceConsequences.lean:46), with `hCC` specialised at α₀ = 0. The conclusion and the other binders are those of `firstPass_8_2_S8d_noWeyl_derivedInputs19`. -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputs23
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : TypicalPointManyGoodScalesStmt.{u} :=
  HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs19 (hL1 := hL1) (hfull := (HarmonicBalls.lqgMeasureFullSupportStmt_of_existence (hDG := hDG) (hCC := fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) (hE := hEx))) (hDG := hDG) (hEx := hEx) (hCC := hCC) (hE3 := hE3)

end HarmonicBalls

