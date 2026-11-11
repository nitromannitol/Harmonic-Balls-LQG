import HarmonicBalls.FirstPass.Closure.Main12CanonicalOf13
import HarmonicBalls.FirstPass.Closure.Sec11CanonicalOf13
import HarmonicBalls.FirstPass.Phase2.DerivedInputs19
import HarmonicBalls.FirstPass.Phase2.DerivedInputs21
import HarmonicBalls.FirstPass.Phase2.DerivedInputs28
import HarmonicBalls.FirstPass.Phase2.DerivedInputs33
import HarmonicBalls.FirstPass.Phase2.DerivedInputs5
import HarmonicBalls.FirstPass.Phase2.DerivedInputsSec11A
import HarmonicBalls.FirstPass.Phase2.PhaseTorusErgodicDerived

/-!
# Derived-input forms, round 36: proved inputs supplied

Each theorem below is the declaration named in its docstring with one hypothesis removed: the hypothesis is a
literature input which is now a theorem. Statements are otherwise copied verbatim; the proofs are applications.
Proved inputs supplied here:
* `PhaseTorusDoublingProductErgodicFrozen` by `phaseTorusDoublingProductErgodicFrozen_holds` (the ergodicity of the doubling map of the phase torus times an ergodic map).

Generated from the signatures of the wrapped declarations; do not edit by hand.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- `TypicalPointManyGoodScalesStmt` from `firstPass_8_2_S8d_noWeyl_derivedInputs33`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputs36
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    : TypicalPointManyGoodScalesStmt.{u} :=
  firstPass_8_2_S8d_noWeyl_derivedInputs33 hSub hDG hEx hCC phaseTorusDoublingProductErgodicFrozen_holds

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- `AnnulusMassBoundByHarmonicChainStmt` from `closure_11_6_derivedInputs33`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_11_6_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    : AnnulusMassBoundByHarmonicChainStmt.{u} :=
  closure_11_6_derivedInputs33 hDG hCC hE hSub phaseTorusDoublingProductErgodicFrozen_holds

/-- `BoundaryMeasureZeroOfCompactClusterStmt` from `closure_8_1_derivedInputs19`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_8_1_derivedInputs36
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : BoundaryMeasureZeroOfCompactClusterStmt.{u} :=
  closure_8_1_derivedInputs19 hL1 phaseTorusDoublingProductErgodicFrozen_holds hDG hCC hE

/-- `HarmonicBallNoveltyFaithfulStmt` from `closure_1_2_faithful_derivedInputs28`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_1_2_faithful_derivedInputs36
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
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hStep8 : Step8IdentificationStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyFaithfulStmt.{u} :=
  closure_1_2_faithful_derivedInputs28 hDG hAff hCC hW hE hN hL1 hE1 phaseTorusDoublingProductErgodicFrozen_holds hCamp hCM hAx hStep8 hTor

/-- `ClusterBoundaryMeasureZeroStmt` from `closure_5_3_derivedInputs19`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_5_3_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    : ClusterBoundaryMeasureZeroStmt.{u} :=
  closure_5_3_derivedInputs19 hDG hCC hE hL1 phaseTorusDoublingProductErgodicFrozen_holds

/-- `ClusterContinuityStmt` from `closure_5_2_derivedInputs33`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_5_2_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    : ClusterContinuityStmt.{u} :=
  closure_5_2_derivedInputs33 hDG hCC hE hSub phaseTorusDoublingProductErgodicFrozen_holds

/-- `ClusterTimeContinuityStmt` from `closure_7_2_derivedInputs19`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_7_2_derivedInputs36
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : ClusterTimeContinuityStmt.{u} :=
  closure_7_2_derivedInputs19 hL1 phaseTorusDoublingProductErgodicFrozen_holds hDG hCC hE

/-- `ExistenceHarmonicBallsStmt` from `closure_5_5_derivedInputs19`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_5_5_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    : ExistenceHarmonicBallsStmt.{u} :=
  closure_5_5_derivedInputs19 hDG hCC hE hL1 phaseTorusDoublingProductErgodicFrozen_holds

/-- `ExistenceUniquenessHarmonicBallsStmt` from `closure_1_1_derivedInputs19`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_1_1_derivedInputs36
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : ExistenceUniquenessHarmonicBallsStmt.{u} :=
  closure_1_1_derivedInputs19 hL1 phaseTorusDoublingProductErgodicFrozen_holds hDG hCC hE

/-- `HarmonicBallComplementBoundaryJordanStmt` from `closure_10_7_derivedInputs19`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_10_7_derivedInputs36
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallComplementBoundaryJordanStmt.{u} :=
  closure_10_7_derivedInputs19 hL1 phaseTorusDoublingProductErgodicFrozen_holds hDG hCC hE hTor

/-- `HarmonicBallLocalSetStmt` from `closure_1_3_derivedInputs21`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_1_3_derivedInputs36
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : HarmonicBallLocalSetStmt.{u} :=
  closure_1_3_derivedInputs21 hL1 phaseTorusDoublingProductErgodicFrozen_holds hDG hCC hE

/-- `HarmonicBallNotLipschitzStmt` from `closure_11_2_derivedInputs28`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_11_2_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    : HarmonicBallNotLipschitzStmt.{u} :=
  closure_11_2_derivedInputs28 hDG hCC hE hL1 phaseTorusDoublingProductErgodicFrozen_holds hCamp hCM

/-- `HarmonicBallNotMetricBallCanonicalStmt` from `closure_11_11_canonical_of_11_13`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_11_11_canonical_of_11_13_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u}) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  closure_11_11_canonical_of_11_13 hDG hCC hE hW hN hL1 hE1 phaseTorusDoublingProductErgodicFrozen_holds hB hAx h13

/-- `HarmonicBallNotMetricBallCanonicalStmt` from `closure_11_11_paperExponent_of_11_13_derivedInputs`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_11_11_paperExponent_of_11_13_derivedInputs36
    (_hDim : WholePlaneLQGGraphDimension)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    : HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  closure_11_11_paperExponent_of_11_13_derivedInputs _hDim hDG hCC hE hW hN hL1 hE1 phaseTorusDoublingProductErgodicFrozen_holds hAx h13

/-- `HarmonicBallNotMetricBallCanonicalStmt` from `firstPass_11_11_faithful`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem firstPass_11_11_faithful_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u}) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  firstPass_11_11_faithful hDG hCC hE hW hN hL1 hE1 phaseTorusDoublingProductErgodicFrozen_holds hB hAx h13

/-- `HarmonicBallNotMetricBallStmt` from `closure_11_11_derivedInputs5`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_11_11_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hStep8 : Step8IdentificationStmt.{u})
    : HarmonicBallNotMetricBallStmt.{u} :=
  closure_11_11_derivedInputs5 hDG hCC hE hW hN hL1 hE1 phaseTorusDoublingProductErgodicFrozen_holds hAx hStep8

/-- `HarmonicBallNoveltyCanonicalStmt` from `closure_1_2_canonical_of_11_13_clean`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_1_2_canonical_of_11_13_clean_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
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
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (h13 : CorrectedLemma11_13CanonicalStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyCanonicalStmt.{u} :=
  closure_1_2_canonical_of_11_13_clean hDG hCC hW hE hN hL1 hE1 phaseTorusDoublingProductErgodicFrozen_holds hB hCamp hDec hCM hAx h13 hTor

/-- `HarmonicBallNoveltyStmt` from `closure_1_2_derivedInputs28`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_1_2_derivedInputs36
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
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hStep8 : Step8IdentificationStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallNoveltyStmt.{u} :=
  closure_1_2_derivedInputs28 hDG hAff hCC hW hE hN hL1 hE1 phaseTorusDoublingProductErgodicFrozen_holds hCamp hCM hAx hStep8 hTor

/-- `NoConeConditionStmt` from `closure_11_5_derivedInputs28`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_11_5_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    : NoConeConditionStmt.{u} :=
  closure_11_5_derivedInputs28 hDG hCC hE hL1 phaseTorusDoublingProductErgodicFrozen_holds hCamp hCM

/-- `RegularizedClusterHarmonicBallsStmt` from `closure_5_4_derivedInputs19`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_5_4_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    : RegularizedClusterHarmonicBallsStmt.{u} :=
  closure_5_4_derivedInputs19 hDG hCC hE hL1 phaseTorusDoublingProductErgodicFrozen_holds

/-- `SubharmonicBallUniquenessC51Stmt` from `closure_9_2_derivedInputs33`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem closure_9_2_derivedInputs36
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : HarmonicBalls.S9c.SubharmonicBallUniquenessC51Stmt.{u} :=
  closure_9_2_derivedInputs33 hSub phaseTorusDoublingProductErgodicFrozen_holds hDG hCC hE

/-- `TypicalPointManyGoodScalesStmt` from `typicalPointManyGoodScales_closed_derivedInputs19`, with the input `PhaseTorusDoublingProductErgodicFrozen` (the ergodicity of the doubling map of the phase torus times an ergodic map, `phaseTorusDoublingProductErgodicFrozen_holds`) supplied. -/
theorem typicalPointManyGoodScales_closed_derivedInputs36
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    : TypicalPointManyGoodScalesStmt.{u} :=
  typicalPointManyGoodScales_closed_derivedInputs19 hDG hCC hE hL1 phaseTorusDoublingProductErgodicFrozen_holds

end HarmonicBalls.Closure
