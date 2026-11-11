import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.LPBridge.LQGMeasureSquarePositive
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.FirstPass.Phase2.DerivedInputs28
import HarmonicBalls.FirstPass.Phase2.DerivedInputs29

/-!
# Row 23 from rows 1, 2, 3

`LQGMeasureSquarePositiveFrozen` (FirstPass/Frozen/S11c.lean:130). The LP route is
`lqgMeasureSquarePositiveFrozen_of_lpStage` (FirstPass/LPBridge/LQGMeasureSquarePositive.lean:30), which takes the LP forms of
rows 1, 2, 3 (`LatticeProb.LQG.LQGMeasureExistenceLP`, `LQGMeasureCoordChangeLP`, `WholePlaneLQGBallMassBoundsLP`,
LatticeProb/LQG/LQGMeasureInputs.lean). The HB Props of Proposed/LQG.lean are transported to the LP forms here:
the definitions `PolyHighProb`, `lqgQ`, `fieldCircleAverage` and `IsClosedDyadicSquare` have identical bodies in both copies,
and `IsWholePlaneGFF`, `IsLQGMeasureOfField`, `IsLQGLimit` are transported by the bridge equivalences
`isWholePlaneGFF_iff` (M1), `isLQGMeasureOfField_iff` and `isLQGLimit_iff` (M4).
-/

open MeasureTheory

universe u

namespace HarmonicBalls

/-- Row 1 (HB form, every `α`) transported to the LP form `LatticeProb.LQG.LQGMeasureExistenceLP`. -/
theorem lqgMeasureExistenceLP_of_HB {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (h : LQGMeasureExistence P γ α hC hcirc) :
    LatticeProb.LQG.LQGMeasureExistenceLP P γ α hC hcirc := by
  intro hG hγ hγ2 hα
  obtain ⟨μ, hμ⟩ := h ((LPBridge.isWholePlaneGFF_iff P hC hcirc).2 hG) hγ hγ2 hα
  exact ⟨μ, (LPBridge.isLQGMeasureOfField_iff P γ α hcirc μ).1 hμ⟩

/-- Row 3 (HB form) transported to the LP form `LatticeProb.LQG.WholePlaneLQGBallMassBoundsLP`. -/
theorem wholePlaneLQGBallMassBoundsLP_of_HB {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (h : WholePlaneLQGBallMassBounds P γ hC hcirc) :
    LatticeProb.LQG.WholePlaneLQGBallMassBoundsLP P γ hC hcirc := by
  intro hG hγ hγ2 μ hμ βl βu h1 h2 h3
  exact h ((LPBridge.isWholePlaneGFF_iff P hC hcirc).2 hG) hγ hγ2 μ
    ((LPBridge.isLQGMeasureOfField_iff P γ 0 hcirc μ).2 hμ) βl βu h1 h2 h3

/-- Row 2 (HB form, `α₀` free) transported to the LP form `LatticeProb.LQG.LQGMeasureCoordChangeLP`. -/
theorem lqgMeasureCoordChangeLP_of_HB {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (h : LQGMeasureCoordChange P γ α₀ hC hcirc) :
    LatticeProb.LQG.LQGMeasureCoordChangeLP P γ α₀ hC hcirc := by
  intro hG hγ hγ2 hα μ hμ
  filter_upwards [h ((LPBridge.isWholePlaneGFF_iff P hC hcirc).2 hG) hγ hγ2 hα μ
    ((LPBridge.isLQGMeasureOfField_iff P γ α₀ hcirc μ).2 hμ)] with ω hω a ha b
  exact (LPBridge.isLQGLimit_iff _ _ _).1 (hω a ha b)

/-- Row 23 (`LQGMeasureSquarePositiveFrozen`, FirstPass/Frozen/S11c.lean:130) from the HB forms of rows 1, 2, 3. -/
theorem lqgMeasureSquarePositiveFrozen_of_rows123
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    LQGMeasureSquarePositiveFrozen.{u} :=
  lqgMeasureSquarePositiveFrozen_of_lpStage
    (fun Ω _ P γ hC hcirc => wholePlaneLQGBallMassBoundsLP_of_HB P γ hC hcirc (hDG Ω P γ hC hcirc))
    (fun Ω _ P γ hC hcirc => lqgMeasureCoordChangeLP_of_HB P γ 0 hC hcirc (hCC Ω P γ hC hcirc))
    (fun Ω _ P γ α hC hcirc => lqgMeasureExistenceLP_of_HB P γ α hC hcirc (hE Ω P γ α hC hcirc))

end HarmonicBalls
-- generated blocks

-- DI30: closure_11_11_canonical_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:32)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_11_11_canonical_derivedInputs28` of `closure_11_11_canonical_derivedInputs22`.
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_11_canonical_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : HarmonicBallNotMetricBallCanonicalStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_11_canonical_derivedInputs22 (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{u} hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE)) (hSupM := hSupM) (hFin := hFin) (hId := hId)

end HarmonicBalls.Closure

-- DI30: closure_11_11_canonical_of_11_13_universe0_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:67)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_11_11_canonical_of_11_13_universe0_derivedInputs28` of `closure_11_11_canonical_of_11_13_universe0_derivedInputs22`.
  Binders discharged by derived theorems: hLoc, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_11_canonical_of_11_13_universe0_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    : HarmonicBallNotMetricBallCanonicalStmt.{0}
  :=
  HarmonicBalls.Closure.closure_11_11_canonical_of_11_13_universe0_derivedInputs22 (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{0} hDG (fun Ω _ P γ hC hcirc => hCC γ 0 Ω P hC hcirc) hE)) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

end HarmonicBalls.Closure

-- DI30: closure_11_11_paperExponent_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:104)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_11_11_paperExponent_derivedInputs28` of `closure_11_11_paperExponent_derivedInputs22`.
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_11_paperExponent_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : HarmonicBallNotMetricBallCanonicalStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_11_paperExponent_derivedInputs22 (_hDim := _hDim) (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{u} hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE)) (hSupM := hSupM) (hFin := hFin) (hId := hId)

end HarmonicBalls.Closure

-- DI30: closure_11_11_paperExponent_of_11_13_universe0_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:140)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs28` of `closure_11_11_paperExponent_of_11_13_universe0_derivedInputs22`.
  Binders discharged by derived theorems: hLoc, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_11_paperExponent_of_11_13_universe0_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    : HarmonicBallNotMetricBallCanonicalStmt.{0}
  :=
  HarmonicBalls.Closure.closure_11_11_paperExponent_of_11_13_universe0_derivedInputs22 (_hDim := _hDim) (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{0} hDG (fun Ω _ P γ hC hcirc => hCC γ 0 Ω P hC hcirc) hE)) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

end HarmonicBalls.Closure

-- DI30: closure_11_12_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:178)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_11_12_derivedInputs28` of `closure_11_12_derivedInputs22`.
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_12_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    : CorrectedLemma11_12Stmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_12_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{u} hDG hCC hE)) (hSupM := hSupM) (hFin := hFin)

end HarmonicBalls.Closure

-- DI30: closure_11_12_clean_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:210)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_11_12_clean_derivedInputs28` of `closure_11_12_clean_derivedInputs22`.
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_12_clean_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    : CorrectedLemma11_12CleanStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_12_clean_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{u} hDG hCC hE)) (hSupM := hSupM) (hFin := hFin)

end HarmonicBalls.Closure

-- DI30: closure_11_13_canonical_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:242)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_11_13_canonical_derivedInputs28` of `closure_11_13_canonical_derivedInputs22`.
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_13_canonical_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : CorrectedLemma11_13CanonicalStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_13_canonical_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{u} hDG hCC hE)) (hSupM := hSupM) (hFin := hFin) (hId := hId)

end HarmonicBalls.Closure

-- DI30: closure_11_13_paperExponent_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:275)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_11_13_paperExponent_derivedInputs28` of `closure_11_13_paperExponent_derivedInputs22`.
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_11_13_paperExponent_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : CorrectedLemma11_13CanonicalStmt.{u}
  :=
  HarmonicBalls.Closure.closure_11_13_paperExponent_derivedInputs22 (_hDim := _hDim) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{u} hDG hCC hE)) (hSupM := hSupM) (hFin := hFin) (hId := hId)

end HarmonicBalls.Closure

-- DI30: closure_1_2_canonical_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:376)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_1_2_canonical_derivedInputs28` of `closure_1_2_canonical_derivedInputs22`.
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_canonical_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyCanonicalStmt.{u}
  :=
  HarmonicBalls.Closure.closure_1_2_canonical_derivedInputs22 (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hN2 := hN2) (hCanon := hCanon) (hExists := hExists) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{u} hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE)) (hSupM := hSupM) (hFin := hFin) (hId := hId) (hTor := hTor)

end HarmonicBalls.Closure

-- DI30: closure_1_2_faithful_canonical_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:482)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_1_2_faithful_canonical_derivedInputs28` of `closure_1_2_faithful_canonical_derivedInputs22`.
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_faithful_canonical_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyFaithfulStmt.{u}
  :=
  HarmonicBalls.Closure.closure_1_2_faithful_canonical_derivedInputs22 (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hN2 := hN2) (hCanon := hCanon) (hExists := hExists) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{u} hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE)) (hSupM := hSupM) (hFin := hFin) (hId := hId) (hTor := hTor)

end HarmonicBalls.Closure

-- DI30: closure_1_2_paperExponent_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:559)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `closure_1_2_paperExponent_derivedInputs28` of `closure_1_2_paperExponent_derivedInputs22`.
  Binders discharged by derived theorems: hDec (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem closure_1_2_paperExponent_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyFaithfulStmt.{u}
  :=
  HarmonicBalls.Closure.closure_1_2_paperExponent_derivedInputs22 (_hDim := _hDim) (hDG := hDG) (hCC := hCC) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCM := hCM) (hAx := hAx) (hN2 := hN2) (hCanon := hCanon) (hExists := hExists) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{u} hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE)) (hSupM := hSupM) (hFin := hFin) (hId := hId) (hTor := hTor)

end HarmonicBalls.Closure

-- DI30: firstPass_11_11_faithful_universe0_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:669)
namespace HarmonicBalls.Closure
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `firstPass_11_11_faithful_universe0_derivedInputs28` of `firstPass_11_11_faithful_universe0_derivedInputs22`.
  Binders discharged by derived theorems: hLoc, hK (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_11_faithful_universe0_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hRootCont : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    : HarmonicBallNotMetricBallCanonicalStmt.{0}
  :=
  HarmonicBalls.Closure.firstPass_11_11_faithful_universe0_derivedInputs22 (hDG := hDG) (hE := hE) (hL1 := hL1) (hE3 := hE3) (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanonM := hCanonM) (hExists := hExists) (hCC := hCC) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{0} hDG (fun Ω _ P γ hC hcirc => hCC γ 0 Ω P hC hcirc) hE)) (hSupM := hSupM) (hFin := hFin) (hRootCont := hRootCont) (hA10 := hA10) (hK := HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived)

end HarmonicBalls.Closure

-- DI30: firstPass_11_13_final_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:855)
namespace HarmonicBalls.FirstPassS11iFinal11_13
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `firstPass_11_13_final_derivedInputs28` of `firstPass_11_13_final_derivedInputs22`.
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_13_final_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hIns : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferStmt)
    : CorrectedLemma11_13CanonicalStmt.{0}
  :=
  HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC0 := hCC0) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{0} hDG (fun Ω _ P γ hC hcirc => hCC0 γ Ω P hC hcirc) hE)) (hSupM := hSupM) (hFin := hFin) (hCal := hCal) (hIns := hIns)

end HarmonicBalls.FirstPassS11iFinal11_13

-- DI30: firstPass_11_13_final_route1_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:888)
namespace HarmonicBalls.FirstPassS11iFinal11_13
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `firstPass_11_13_final_route1_derivedInputs28` of `firstPass_11_13_final_route1_derivedInputs22`.
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_13_final_route1_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0})
    (hCal : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8EventCalibrationStmt.{0})
    (hK0 : HarmonicBalls.FirstPassS11iStep8PhysExists.Step8InsertionTransferK0Stmt)
    : CorrectedLemma11_13CanonicalStmt.{0}
  :=
  HarmonicBalls.FirstPassS11iFinal11_13.firstPass_11_13_final_route1_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{0} hDG (fun Ω _ P γ hC hcirc => hCC γ 0 Ω P hC hcirc) hE)) (hSupM := hSupM) (hFin := hFin) (hCal := hCal) (hK0 := hK0)

end HarmonicBalls.FirstPassS11iFinal11_13

-- DI30: firstPass_11_13_canonical_derivedInputs28 with hPos10 traded for rows 1-3 (source DerivedInputs28.lean:929)
namespace HarmonicBalls.FirstPassS11iAssembly11_13
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
/-- Binder-trade wrapper `firstPass_11_13_canonical_derivedInputs28` of `firstPass_11_13_canonical_derivedInputs22`.
  Binders discharged by derived theorems: hLoc (`HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived` for
  `LocalLQGDecoderCommonFrozen`, `HarmonicBalls.LocalDecoderCommon.localMeasureKernelStmt_derived` for `LocalMeasureKernelStmt`).
  Other binders and the conclusion unchanged. -/
theorem firstPass_11_13_canonical_derivedInputs30
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
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u})
    : CorrectedLemma11_13CanonicalStmt.{u}
  :=
  HarmonicBalls.FirstPassS11iAssembly11_13.firstPass_11_13_canonical_derivedInputs22 (hAx := hAx) (hN2 := hN2) (hLoc := HarmonicBalls.LocalDecoderCommon.localLQGDecoderCommonFrozen_derived) (hCanon := hCanon) (hExists := hExists) (hDG := hDG) (hCC := hCC) (hE := hE) (hfr := hfr) (hComp := hComp) (hFA := hFA) (hMk := hMk) (hholder := hholder) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := (HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{u} hDG hCC hE)) (hSupM := hSupM) (hFin := hFin) (hId := hId)

end HarmonicBalls.FirstPassS11iAssembly11_13

-- DI30: firstPass_11_13_closed_derivedInputs29 with hPos10 traded for rows 1-3 (source DerivedInputs29.lean:109)
namespace HarmonicBalls.FirstPassS11iFinal11_13Close
open MeasureTheory Metric Set Filter Topology
open HarmonicBalls.FirstPassS11iFinal11_13
/-- Binder trade of `firstPass_11_13_closed_derivedInputs3` (DerivedInputs3.lean:165): the binders `hFull` and
`hgrowth` are derived from `hDG`, `hCCα` (at `α₀ = 0`) and `hE`, which the wrapper already binds. Binder count 37 → 35. -/
theorem firstPass_11_13_closed_derivedInputs30
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
  HarmonicBalls.FirstPassS11iFinal11_13Close.firstPass_11_13_closed_derivedInputs2 hAx hLen hN2 hμW hLoc hCanonM
    hNonat hExists hDG hCCα hE hfr hmass hCMAbs hCMRew hComp hMf hDiam hMk hholder hShift hFD hDC hCMT ((HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_rows123.{0} hDG (fun Ω _ P γ hC hcirc => hCCα γ 0 Ω P hC hcirc) hE))
    (HarmonicBalls.lqgMeasureSquareMeasurable_derived.{0} hmeasure) hSupM hFin HarmonicBalls.weylInternalClosed_derived
    hM1 hRootCont hProf hWCont hA10
    (HarmonicBalls.lqgMeasureFullSupportStmt_of_rows123.{0} hDG (fun Ω _ P γ hC hcirc => hCCα γ 0 Ω P hC hcirc) hE)
    (HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_rows123.{0} hDG (fun Ω _ P γ hC hcirc => hCCα γ 0 Ω P hC hcirc) hE)
    hDsm hK

end HarmonicBalls.FirstPassS11iFinal11_13Close

