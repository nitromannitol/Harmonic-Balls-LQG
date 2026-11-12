import HarmonicBalls.FirstPass.Closure.Main12Canonical
import HarmonicBalls.FirstPass.Main
import HarmonicBalls.FirstPass.Phase2.DerivedInputs36
import HarmonicBalls.FirstPass.Phase2.DerivedInputs43
import HarmonicBalls.FirstPass.Phase2.TorhorstDerived
import HarmonicBalls.FirstPass.S1S10.CrossingLemma

/-!
# Derived-input forms, round 46: proved inputs supplied

Each theorem below is the declaration named in its docstring with one hypothesis removed: the hypothesis is a
literature input which is now a theorem. Statements are otherwise copied verbatim; the proofs are applications.
Proved inputs supplied here:
* `TorhorstSimpleLoopFrozen` by `torhorstSimpleLoopFrozen_holds` (Torhorst's theorem on simple-loop frontiers).

Generated from the signatures of the wrapped declarations; do not edit by hand.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- `ComplementComponentBoundarySimpleLoopStmt` from `firstPass_10_6_derivedInputs43`, with the input `TorhorstSimpleLoopFrozen` (Torhorst's theorem on simple-loop frontiers, `torhorstSimpleLoopFrozen_holds`) supplied. -/
theorem firstPass_10_6_derivedInputs46 :
    ComplementComponentBoundarySimpleLoopStmt.{u} :=
  firstPass_10_6_derivedInputs43 torhorstSimpleLoopFrozen_holds

/-- `HarmonicBallNoveltyCanonicalStmt` from `firstPassMain_1_2_canonical`, with the input `TorhorstSimpleLoopFrozen` (Torhorst's theorem on simple-loop frontiers, `torhorstSimpleLoopFrozen_holds`) supplied. -/
theorem firstPassMain_1_2_canonical_derivedInputs46
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hTyp : TypicalPointManyGoodScalesStmt.{u})
    (h7 : ManyConeBadScalesStmt.{u})
    (h13 : HarmonicBalls.Closure.ManyPinchScalesCanonicalModelStmt.{u})
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNoveltyCanonicalStmt.{u} :=
  firstPassMain_1_2_canonical hDG hAff hCC hW hE hN hI2 hTyp h7 h13 torhorstSimpleLoopFrozen_holds hmetricAxioms

/-- `HarmonicBallNoveltyStmt` from `firstPassMain_1_2`, with the input `TorhorstSimpleLoopFrozen` (Torhorst's theorem on simple-loop frontiers, `torhorstSimpleLoopFrozen_holds`) supplied. -/
theorem firstPassMain_1_2_derivedInputs46
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hTyp : TypicalPointManyGoodScalesStmt.{u})
    (h7 : ManyConeBadScalesStmt.{u})
    (h13 : ManyPinchScalesStmt.{u})
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPassMain_1_2 hDG hAff hCC hW hE hN hI2 hTyp h7 h13 torhorstSimpleLoopFrozen_holds hmetricAxioms

/-- Lemma 10.5 (corrected form [C48], inline conclusion) from `firstPass_10_5_corrected`, with the input `TorhorstSimpleLoopFrozen` (Torhorst's theorem on simple-loop frontiers, `torhorstSimpleLoopFrozen_holds`) supplied. -/
theorem firstPass_10_5_corrected_derivedInputs46 {G : Set ℂ} (hGne : G.Nonempty) (hGb : Bornology.IsBounded G)
    (hGo : IsOpen G) (hGc : IsConnected G)
    (hEcross : ∃ E : Set ℂ, E.Finite ∧ ∀ p ∈ frontier G \ E, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
      (crossingComponents (G ∩ ball p (2 * r)) p (r / 3) (2 * r)).Finite) :
    IsLocallyConnectedSet (closure G) ∧ (∀ a : ℂ, ¬ IsCutPoint (closure G) a) ∧
      ∀ C ∈ connectedComponentsIn (closure G)ᶜ, IsSimpleLoop (frontier C) :=
  firstPass_10_5_corrected hGne hGb hGo hGc hEcross torhorstSimpleLoopFrozen_holds

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- `HarmonicBallNoveltyFaithfulStmt` from `closure_1_2_faithful_derivedInputs36`, with the input `TorhorstSimpleLoopFrozen` (Torhorst's theorem on simple-loop frontiers, `torhorstSimpleLoopFrozen_holds`) supplied. -/
theorem closure_1_2_faithful_derivedInputs46
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
    : HarmonicBallNoveltyFaithfulStmt.{u} :=
  closure_1_2_faithful_derivedInputs36 hDG hAff hCC hW hE hN hL1 hE1 hCamp hCM hAx hStep8 torhorstSimpleLoopFrozen_holds

/-- `HarmonicBallComplementBoundaryJordanStmt` from `closure_10_7_derivedInputs43`, with the input `TorhorstSimpleLoopFrozen` (Torhorst's theorem on simple-loop frontiers, `torhorstSimpleLoopFrozen_holds`) supplied. -/
theorem closure_10_7_derivedInputs46 :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  closure_10_7_derivedInputs43 torhorstSimpleLoopFrozen_holds

end HarmonicBalls.Closure
