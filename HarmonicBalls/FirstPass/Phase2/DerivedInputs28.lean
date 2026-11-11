import HarmonicBalls.FirstPass.Phase2.DerivedInputs19
import HarmonicBalls.FirstPass.Phase2.DerivedInputs21
import HarmonicBalls.FirstPass.Phase2.DerivedInputs22
import HarmonicBalls.FirstPass.Phase2.DerivedInputs27
import HarmonicBalls.FirstPass.Phase2.DerivedInputs5
import HarmonicBalls.FirstPass.Phase2.DerivedInputsSec1to10
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived

/-!
# Binder trade hLoc/hDec/hK (DerivedInputs28; task fp-phase2-di28-decoder-trades, worker z4)

Each wrapper `..._derivedInputs28` is the newest counted wrapper (DerivedInputs27, or the newest older generation that wraps
the same form) with every binder of type `LocalLQGDecoderCommonFrozen` (hLoc, hDec) or `LocalMeasureKernelStmt` (hK) removed.
Those binders are discharged by the derived theorems `HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived`
(FirstPass/Phase2/LocalDecoderCommonDerived.lean, commit 9deeaee0) and `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived`
(same file, commit a9b0d406). All other binders and the conclusion are unchanged, so no binder count increases.
-/

open scoped ENNReal

universe u

namespace HarmonicBalls.Closure

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `closure_11_11_canonical_derivedInputs28` of `closure_11_11_canonical_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_11_canonical_derivedInputs28
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
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : HarmonicBallNotMetricBallCanonicalStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_11_canonical_derivedInputs22 (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hId := hId)

/-- Binder-trade wrapper `closure_11_11_canonical_of_11_13_universe0_derivedInputs28` of `closure_11_11_canonical_of_11_13_universe0_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_11_canonical_of_11_13_universe0_derivedInputs28
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
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
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    : HarmonicBallNotMetricBallCanonicalStmt.{0}
  :=
  HarmonicBalls.Closure.closure_11_11_canonical_of_11_13_universe0_derivedInputs22 (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

/-- Binder-trade wrapper `closure_11_11_paperExponent_derivedInputs28` of `closure_11_11_paperExponent_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_11_paperExponent_derivedInputs28
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
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : HarmonicBallNotMetricBallCanonicalStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_11_paperExponent_derivedInputs22 (_hDim := _hDim) (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hId := hId)

/-- Binder-trade wrapper `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs28` of `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_11_paperExponent_of_11_13_universe0_derivedInputs28
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
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    : HarmonicBallNotMetricBallCanonicalStmt.{0}
  :=
  HarmonicBalls.Closure.closure_11_11_paperExponent_of_11_13_universe0_derivedInputs22 (_hDim := _hDim) (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

/-- Binder-trade wrapper `closure_11_12_derivedInputs28` of `closure_11_12_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_12_derivedInputs28
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    : CorrectedLemma11_12Stmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_12_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin)

/-- Binder-trade wrapper `closure_11_12_clean_derivedInputs28` of `closure_11_12_clean_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_12_clean_derivedInputs28
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    : CorrectedLemma11_12CleanStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_12_clean_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin)

/-- Binder-trade wrapper `closure_11_13_canonical_derivedInputs28` of `closure_11_13_canonical_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_13_canonical_derivedInputs28
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : CorrectedLemma11_13CanonicalStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_13_canonical_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hId := hId)

/-- Binder-trade wrapper `closure_11_13_paperExponent_derivedInputs28` of `closure_11_13_paperExponent_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_13_paperExponent_derivedInputs28
    (_hDim : WholePlaneLQGGraphDimension)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : CorrectedLemma11_13CanonicalStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_13_paperExponent_derivedInputs22 (_hDim := _hDim) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hId := hId)

/-- Binder-trade wrapper `closure_11_2_derivedInputs28` of `closure_11_2_derivedInputs19` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_2_derivedInputs28
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    : HarmonicBallNotLipschitzStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_2_derivedInputs19 (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM)

/-- Binder-trade wrapper `closure_11_5_derivedInputs28` of `closure_11_5_derivedInputs19` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_5_derivedInputs28
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    : NoConeConditionStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_5_derivedInputs19 (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM)

/-- Binder-trade wrapper `closure_1_2_derivedInputs28` of `closure_1_2_derivedInputs5` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_derivedInputs28
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hStep8 : Step8IdentificationStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyStmt.{u}
  :=
  HarmonicBalls.Closure.closure_1_2_derivedInputs5 (hDG := hDG) (hAff := hAff) (hCC := hCC) (hW := hW) (hE := hE) (hN := hN) (hL1 := hL1) (hE1 := hE1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hStep8 := hStep8) (hTor := hTor)

/-- Binder-trade wrapper `closure_1_2_canonical_derivedInputs28` of `closure_1_2_canonical_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_canonical_derivedInputs28
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
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
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyCanonicalStmt.{u}
  :=
  HarmonicBalls.Closure.closure_1_2_canonical_derivedInputs22 (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hN2 := hN2) (hCanon := hCanon) (hExists := hExists) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hId := hId) (hTor := hTor)

/-- Binder-trade wrapper `closure_1_2_canonical_of_11_13_universe0_derivedInputs28` of `closure_1_2_canonical_of_11_13_universe0_derivedInputs27` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_canonical_of_11_13_universe0_derivedInputs28
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{0})
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
    : HarmonicBallNoveltyCanonicalStmt.{0}
  :=
  HarmonicBalls.Closure.closure_1_2_canonical_of_11_13_universe0_derivedInputs27 (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hTor := hTor) (hN2 := hN2) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

/-- Binder-trade wrapper `closure_1_2_faithful_derivedInputs28` of `closure_1_2_faithful_derivedInputs5` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_faithful_derivedInputs28
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hStep8 : Step8IdentificationStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyFaithfulStmt.{u}
  :=
  HarmonicBalls.Closure.closure_1_2_faithful_derivedInputs5 (hDG := hDG) (hAff := hAff) (hCC := hCC) (hW := hW) (hE := hE) (hN := hN) (hL1 := hL1) (hE1 := hE1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hStep8 := hStep8) (hTor := hTor)

/-- Binder-trade wrapper `closure_1_2_faithful_canonical_derivedInputs28` of `closure_1_2_faithful_canonical_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_faithful_canonical_derivedInputs28
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
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
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyFaithfulStmt.{u}
  :=
  HarmonicBalls.Closure.closure_1_2_faithful_canonical_derivedInputs22 (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hN2 := hN2) (hCanon := hCanon) (hExists := hExists) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hId := hId) (hTor := hTor)

/-- Binder-trade wrapper `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs28` of `closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs27` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs28
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{0})
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
    : HarmonicBallNoveltyFaithfulStmt.{0}
  :=
  HarmonicBalls.Closure.closure_1_2_faithful_canonical_of_11_13_universe0_derivedInputs27 (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hTor := hTor) (hN2 := hN2) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

/-- Binder-trade wrapper `closure_1_2_paperExponent_derivedInputs28` of `closure_1_2_paperExponent_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_paperExponent_derivedInputs28
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
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyFaithfulStmt.{u}
  :=
  HarmonicBalls.Closure.closure_1_2_paperExponent_derivedInputs22 (_hDim := _hDim) (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hN2 := hN2) (hCanon := hCanon) (hExists := hExists) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hId := hId) (hTor := hTor)

/-- Binder-trade wrapper `closure_1_2_paperExponent_of_11_13_derivedInputs28` of `closure_1_2_paperExponent_of_11_13_derivedInputs` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_paperExponent_of_11_13_derivedInputs28
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyFaithfulStmt.{u}
  :=
  HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13_derivedInputs (_hDim := _hDim) (hDG := hDG) (hAff := hAff) (hCC := hCC) (hW := hW) (hE := hE) (hN := hN) (hL1 := hL1) (hE1 := hE1) (hE3 := hE3) (hCamp := hCamp) (hDecFrozen := hDecFrozen) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (h13 := h13) (hTor := hTor)

/-- Binder-trade wrapper `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs28` of `closure_1_2_paperExponent_of_11_13_universe0_derivedInputs27` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_paperExponent_of_11_13_universe0_derivedInputs28
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{0})
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
    : HarmonicBallNoveltyFaithfulStmt.{0}
  :=
  HarmonicBalls.Closure.closure_1_2_paperExponent_of_11_13_universe0_derivedInputs27 (_hDim := _hDim) (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hTor := hTor) (hN2 := hN2) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

/-- Binder-trade wrapper `firstPass_11_11_faithful_universe0_derivedInputs28` of `firstPass_11_11_faithful_universe0_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_11_faithful_universe0_derivedInputs28
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
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
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    : HarmonicBallNotMetricBallCanonicalStmt.{0}
  :=
  HarmonicBalls.Closure.firstPass_11_11_faithful_universe0_derivedInputs22 (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

/-- Binder-trade wrapper `firstPass_1_2_faithful_universe0_derivedInputs28` of `firstPass_1_2_faithful_universe0_derivedInputs27` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hDec, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_1_2_faithful_universe0_derivedInputs28
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{0})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{0})
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
    : HarmonicBallNoveltyFaithfulStmt.{0}
  :=
  HarmonicBalls.Closure.firstPass_1_2_faithful_universe0_derivedInputs27 (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hTor := hTor) (hN2 := hN2) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

end HarmonicBalls.Closure

namespace HarmonicBalls.S11m.Clean11_12

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `firstPass_11_12_clean_derivedInputs28` of `firstPass_11_12_clean_derivedInputs21` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_12_clean_derivedInputs28
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    : CorrectedLemma11_12CleanStmt.{u}
  :=
  HarmonicBalls.S11m.Clean11_12.firstPass_11_12_clean_derivedInputs21 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hDsm := hDsm) (hFA := hFA) (hMk := hMk) (hholder := hholder)

end HarmonicBalls.S11m.Clean11_12

namespace HarmonicBalls.S11m.Final11_12

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `firstPass_11_12_final_derivedInputs28` of `firstPass_11_12_final_derivedInputs21` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_12_final_derivedInputs28
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    : CorrectedLemma11_12Stmt.{u}
  :=
  HarmonicBalls.S11m.Final11_12.firstPass_11_12_final_derivedInputs21 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hDsm := hDsm) (hFA := hFA) (hMk := hMk) (hholder := hholder)

end HarmonicBalls.S11m.Final11_12

namespace HarmonicBalls.FirstPassS11iFinal11_13

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `firstPass_11_13_derivedInputs28` of `firstPass_11_13_derivedInputs27` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_13_derivedInputs28
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
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
    : CorrectedLemma11_13CanonicalStmt.{0}
  :=
  HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_derivedInputs27 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanonM := hCanonM) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hSupM := hSupM) (hFin := hFin) (_hRootCont := _hRootCont) (_hA10 := _hA10) (hCal := hCal) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

/-- Binder-trade wrapper `firstPass_11_13_final_derivedInputs28` of `firstPass_11_13_final_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_13_final_derivedInputs28
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
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
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hIns : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferStmt)
    : CorrectedLemma11_13CanonicalStmt.{0}
  :=
  HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC0 := hCC0) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hCal := hCal) (hIns := hIns)

/-- Binder-trade wrapper `firstPass_11_13_final_route1_derivedInputs28` of `firstPass_11_13_final_route1_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_13_final_route1_derivedInputs28
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
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
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK0 : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferK0Stmt)
    : CorrectedLemma11_13CanonicalStmt.{0}
  :=
  HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final_route1_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hCal := hCal) (hK0 := hK0)

end HarmonicBalls.FirstPassS11iFinal11_13

namespace HarmonicBalls.FirstPassS11iAssembly11_13

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `firstPass_11_13_canonical_derivedInputs28` of `firstPass_11_13_canonical_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_13_canonical_derivedInputs28
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
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
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : CorrectedLemma11_13CanonicalStmt.{u}
  :=
  HarmonicBalls.FirstPassS11iAssembly11_13.firstPass_11_13_canonical_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hId := hId)

end HarmonicBalls.FirstPassS11iAssembly11_13

namespace HarmonicBalls.FirstPassS11iFinal11_13Close

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Binder-trade wrapper `firstPass_11_13_closed_derivedInputs28` of `firstPass_11_13_closed_derivedInputs22` (fp-phase2-di28-decoder-trades, worker z4).
  Binders discharged by derived theorems: hLoc, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_13_closed_derivedInputs28
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementFrozen.{0} γ ξ c₁ c₂ r₁ r₂)
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
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    : CorrectedLemma11_13CanonicalStmt.{0}
  :=
  HarmonicBalls.FirstPassS11iFinal11_13Close.firstPass_11_13_closed_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanonM := hCanonM) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

end HarmonicBalls.FirstPassS11iFinal11_13Close

