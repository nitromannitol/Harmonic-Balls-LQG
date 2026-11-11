import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.Phase2.DerivedInputs22
import HarmonicBalls.FirstPass.Phase2.DerivedInputs28
import HarmonicBalls.FirstPass.Phase2.DerivedInputs30
import HarmonicBalls.FirstPass.Phase2.WeylScalingCompositionDerived
import HarmonicBalls.FirstPass.Phase2.WeylShiftedSupDerived2
import HarmonicBalls.FirstPass.S11d
import HarmonicBalls.FirstPass.S11h.PinchCertificateProof11_17
import HarmonicBalls.FirstPass.S11j.FieldAssembly11_15

/-!
# Derived-input forms, round 37: proved inputs supplied

Each theorem below is the declaration named in its docstring with one hypothesis removed: the hypothesis is a
literature input which is now a theorem. Statements are otherwise copied verbatim; the proofs are applications.
Proved inputs supplied here:
* `WeylScalingCompositionFrozen` by `weylScalingCompositionFrozen_holds` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight).

Generated from the signatures of the wrapped declarations; do not edit by hand.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- `PinchCertificateStmt` from `pinchCertificateStmt_of_frozen`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem pinchCertificateStmt_of_frozen_derivedInputs37
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hdec : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hF : LQGMassFunctionalMeasurableFrozen.{u}) (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hN2 : WeylScaledEuclideanFrozen) : PinchCertificateStmt.{u} :=
  pinchCertificateStmt_of_frozen weylScalingCompositionFrozen_holds hAx hdec hF hK1 hN2

/-- `PinchFirstEventFaithfulStmt` from `firstPass_11_15_corrected`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem firstPass_11_15_corrected_derivedInputs37
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hEx : LQGMetricExponentPositive)
    (haxioms : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchFirstEventFaithfulStmt.{u} :=
  firstPass_11_15_corrected hCM hfr weylScalingCompositionFrozen_holds hEx haxioms

/-- `PinchThirdEventFaithfulStmt` from `firstPass_11_17_corrected`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem firstPass_11_17_corrected_derivedInputs37 (h16 : PinchSecondEventFaithfulStmt.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hCMGFF : CameronMartinGFFMutualAbsCont.{u}) (hdec : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hF : LQGMassFunctionalMeasurableFrozen.{u}) (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hN2 : WeylScaledEuclideanFrozen) : PinchThirdEventFaithfulStmt.{u} :=
  firstPass_11_17_corrected h16 hAx hCMGFF weylScalingCompositionFrozen_holds hdec hF hK1 hN2

/-- `SmallMetricDiameterLargeMassStmt` from `firstPass_11_9`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem firstPass_11_9_derivedInputs37
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hMass : LQGMassFunctionalMeasurableFrozen.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (h1110 : SmallMetricDiameterLargeMassSquareStmt.{u}) :
    SmallMetricDiameterLargeMassStmt.{u} :=
  firstPass_11_9 hCM weylScalingCompositionFrozen_holds hMet hMass hShift hFD hAx h1110

/-- `WeylShiftedSupMeasurableFrozen` from `weylShiftedSupMeasurable_derived`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem weylShiftedSupMeasurable_derived_derivedInputs37
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hInt : LQGInternalMetricWeylAeMeasurableFrozen.{u}) : WeylShiftedSupMeasurableFrozen.{u} :=
  weylShiftedSupMeasurable_derived hAx weylScalingCompositionFrozen_holds hInt

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- `CorrectedLemma11_12CleanStmt` from `closure_11_12_clean_derivedInputs30`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem closure_11_12_clean_derivedInputs37
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
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    : CorrectedLemma11_12CleanStmt.{u} :=
  closure_11_12_clean_derivedInputs30 hAx hN2 hCanon hExists hDG hCC hE hfr weylScalingCompositionFrozen_holds hFA hMk hholder hShift hDC hCMT hSupM hFin

/-- `HarmonicBallNoveltyFaithfulStmt` from `closure_1_2_faithful_canonical_derivedInputs30`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem closure_1_2_faithful_canonical_derivedInputs37
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
    : HarmonicBallNoveltyFaithfulStmt.{u} :=
  closure_1_2_faithful_canonical_derivedInputs30 hDG hCC hE hL1 hE3 hCamp hCM hAx hN2 hCanon hExists hfr weylScalingCompositionFrozen_holds hFA hMk hholder hShift hDC hCMT hSupM hFin hId hTor

/-- `CorrectedLemma11_13CanonicalStmt` from `closure_11_13_canonical_derivedInputs30`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem closure_11_13_canonical_derivedInputs37
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
    : CorrectedLemma11_13CanonicalStmt.{u} :=
  closure_11_13_canonical_derivedInputs30 hAx hN2 hCanon hExists hDG hCC hE hfr weylScalingCompositionFrozen_holds hFA hMk hholder hShift hDC hCMT hSupM hFin hId

/-- `HarmonicBallNotMetricBallCanonicalStmt` from `closure_11_11_canonical_derivedInputs30`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem closure_11_11_canonical_derivedInputs37
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
    : HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  closure_11_11_canonical_derivedInputs30 hDG hCC hE hL1 hE3 hAx hN2 hCanon hExists hfr weylScalingCompositionFrozen_holds hFA hMk hholder hShift hDC hCMT hSupM hFin hId

/-- `HarmonicBallNoveltyCanonicalStmt` from `closure_1_2_canonical_derivedInputs30`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem closure_1_2_canonical_derivedInputs37
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
    : HarmonicBallNoveltyCanonicalStmt.{u} :=
  closure_1_2_canonical_derivedInputs30 hDG hCC hE hL1 hE3 hCamp hCM hAx hN2 hCanon hExists hfr weylScalingCompositionFrozen_holds hFA hMk hholder hShift hDC hCMT hSupM hFin hId hTor

/-- `PinchFirstEventFaithfulStmt` from `closure_11_15`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem closure_11_15_derivedInputs37
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hExists : WholePlaneGFFExistsFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchFirstEventFaithfulStmt.{u} :=
  closure_11_15 hCM hMet weylScalingCompositionFrozen_holds hExists hAx

/-- `PinchSecondEventFaithfulStmt` from `closure_11_16_derivedInputs22`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem closure_11_16_derivedInputs37
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
   : PinchSecondEventFaithfulStmt.{u} :=
  closure_11_16_derivedInputs22 hAx hK1 hholder hEx hNa0 hNa weylScalingCompositionFrozen_holds hMet hExists hShift hDC hCMT hPos10 hSupM hFin hFA hMk

end HarmonicBalls.Closure

namespace HarmonicBalls.FirstPassS11iAssembly11_13

/-- `CorrectedLemma11_13CanonicalStmt` from `firstPass_11_13_canonical_derivedInputs30`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem firstPass_11_13_canonical_derivedInputs37
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
    : CorrectedLemma11_13CanonicalStmt.{u} :=
  firstPass_11_13_canonical_derivedInputs30 hAx hN2 hCanon hExists hDG hCC hE hfr weylScalingCompositionFrozen_holds hFA hMk hholder hShift hDC hCMT hSupM hFin hId

end HarmonicBalls.FirstPassS11iAssembly11_13

namespace HarmonicBalls.S11m.Clean11_12

/-- `CorrectedLemma11_12CleanStmt` from `firstPass_11_12_clean_derivedInputs28`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem firstPass_11_12_clean_derivedInputs37
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    : CorrectedLemma11_12CleanStmt.{u} :=
  firstPass_11_12_clean_derivedInputs28 hAx hN2 hCanon hExists hDG hCC hE hfr weylScalingCompositionFrozen_holds hDsm hFA hMk hholder

end HarmonicBalls.S11m.Clean11_12

namespace HarmonicBalls.S11m.Final11_12

/-- `CorrectedLemma11_12Stmt` from `firstPass_11_12_final_derivedInputs28`, with the input `WeylScalingCompositionFrozen` (the composition rule of Weyl scalings with a continuous inner weight and a logarithmic outer weight, `weylScalingCompositionFrozen_holds`) supplied. -/
theorem firstPass_11_12_final_derivedInputs37
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    : CorrectedLemma11_12Stmt.{u} :=
  firstPass_11_12_final_derivedInputs28 hAx hN2 hCanon hExists hDG hCC hE hfr weylScalingCompositionFrozen_holds hDsm hFA hMk hholder

end HarmonicBalls.S11m.Final11_12
