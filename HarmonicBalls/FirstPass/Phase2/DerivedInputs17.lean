import HarmonicBalls.FirstPass.Phase2.DerivedInputs3
import HarmonicBalls.FirstPass.Phase2.DerivedInputs5
import HarmonicBalls.FirstPass.Phase2.DerivedInputsSec1to10
import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs11
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9
import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived
import HarmonicBalls.FirstPass.Phase2.WeylShiftedMassDerived
import HarmonicBalls.FirstPass.Phase2.PlaneDomainDerived
import HarmonicBalls.FirstPass.Phase2.WeylScaledEuclideanDerived
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! Binder-hygiene wrappers, round 17 (fp-phase2-derived-inputs-17, worker z7).
Scope: counted results outside the DerivedInputs15 family (11.11, 11.12, 11.13, 1.2 are not here).
Each wrapper `<counted>_derivedInputs17` has the statement of the latest wrapper `<counted>_derivedInputsN`
minus every explicit binder whose Prop has a binder-free derived theorem: LQGMeasureOfProfileMeasurableFrozen
(`HarmonicBalls.lqgMeasureOfProfileMeasurable_derived`), LQGMeasureWeylScaling in the universal form with
alpha_0 = 0 (`HarmonicBalls.Section6.lqgMeasureWeylScaling`), WholePlaneGFFAffineInvariance
(`HarmonicBalls.WholePlaneGFFAffineInvariance_derived`), CameronMartinGFFMutualAbsCont
(`HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived`), LQGMassFunctionalMeasurableFrozen
(`HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived`), WeylShiftedMassMeasurableFrozen
(`HarmonicBalls.weylShiftedMassMeasurable_derived`), PlaneDomainMinusConvexCompactPreconnectedFrozen
(`HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived`) and WeylScaledEuclideanFrozen
(`HarmonicBalls.weylScaledEuclidean_derived`). Binders that remain (REDUCIBLE or OPEN-LITERATURE inputs) are kept.
No binder is added. Originals are unchanged. -/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- Binder-hygiene wrapper `firstPass_8_2_S8d_noWeyl_derivedInputs17` of the counted form `firstPass_8_2_S8d_noWeyl` (fp-phase2-derived-inputs-17, worker z7): the binders hAff, hE1 are removed and supplied by the binder-free derived theorems `HarmonicBalls.WholePlaneGFFAffineInvariance_derived`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `firstPass_8_2_S8d_noWeyl_derivedInputs` is unchanged. -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputs17
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u})
    (hL67 : VeryGoodAnnulusProbabilityStmt.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : TypicalPointManyGoodScalesStmt.{u} :=
  HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs (hL1 := hL1) (hfull := hfull)
    (hL67 := hL67) (hEx := hEx) (hN := hN)
    (hAff := HarmonicBalls.WholePlaneGFFAffineInvariance_derived) (hCC := hCC)
    (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) (hE3 := hE3)

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- Binder-hygiene wrapper `closure_1_1_derivedInputs17` of the counted form `closure_1_1` (fp-phase2-derived-inputs-17, worker z7): the binders hE1, hAff, hW are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.WholePlaneGFFAffineInvariance_derived`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_1_1_derivedInputs5` is unchanged. -/
theorem closure_1_1_derivedInputs17
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    : ExistenceUniquenessHarmonicBallsStmt.{u} :=
  HarmonicBalls.Closure.closure_1_1_derivedInputs5 (hL1 := hL1)
    (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) (hE3 := hE3) (hDG := hDG)
    (hAff := HarmonicBalls.WholePlaneGFFAffineInvariance_derived) (hCC := hCC)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hE := hE) (hN := hN)

/-- Binder-hygiene wrapper `closure_1_3_derivedInputs17` of the counted form `closure_1_3` (fp-phase2-derived-inputs-17, worker z7): the binders hE1, hAff, hW are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.WholePlaneGFFAffineInvariance_derived`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_1_3_derivedInputs5` is unchanged. -/
theorem closure_1_3_derivedInputs17
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    : HarmonicBallLocalSetStmt.{u} :=
  HarmonicBalls.Closure.closure_1_3_derivedInputs5 (hmeasure := hmeasure) (hL1 := hL1)
    (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) (hE3 := hE3) (hDG := hDG)
    (hAff := HarmonicBalls.WholePlaneGFFAffineInvariance_derived) (hCC := hCC)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hE := hE) (hN := hN)

/-- Binder-hygiene wrapper `closure_5_2_derivedInputs17` of the counted form `closure_5_2` (fp-phase2-derived-inputs-17, worker z7): the binders hW, hE1 are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_5_2_derivedInputs5` is unchanged. -/
theorem closure_5_2_derivedInputs17
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : ClusterContinuityStmt.{u} :=
  HarmonicBalls.Closure.closure_5_2_derivedInputs5 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hN := hN) (hL1 := hL1) (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    (hE3 := hE3)

/-- Binder-hygiene wrapper `closure_5_3_derivedInputs17` of the counted form `closure_5_3` (fp-phase2-derived-inputs-17, worker z7): the binders hW, hE1 are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_5_3_derivedInputs5` is unchanged. -/
theorem closure_5_3_derivedInputs17
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : ClusterBoundaryMeasureZeroStmt.{u} :=
  HarmonicBalls.Closure.closure_5_3_derivedInputs5 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hN := hN) (hL1 := hL1) (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    (hE3 := hE3)

/-- Binder-hygiene wrapper `closure_5_4_derivedInputs17` of the counted form `closure_5_4` (fp-phase2-derived-inputs-17, worker z7): the binders hW, hE1 are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_5_4_derivedInputs5` is unchanged. -/
theorem closure_5_4_derivedInputs17
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : RegularizedClusterHarmonicBallsStmt.{u} :=
  HarmonicBalls.Closure.closure_5_4_derivedInputs5 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hN := hN) (hL1 := hL1) (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    (hE3 := hE3)

/-- Binder-hygiene wrapper `closure_5_5_derivedInputs17` of the counted form `closure_5_5` (fp-phase2-derived-inputs-17, worker z7): the binders hW, hE1 are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_5_5_derivedInputs5` is unchanged. -/
theorem closure_5_5_derivedInputs17
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : ExistenceHarmonicBallsStmt.{u} :=
  HarmonicBalls.Closure.closure_5_5_derivedInputs5 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hN := hN) (hL1 := hL1) (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    (hE3 := hE3)

/-- Binder-hygiene wrapper `closure_7_2_derivedInputs17` of the counted form `closure_7_2` (fp-phase2-derived-inputs-17, worker z7): the binders hE1, hAff, hW are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.WholePlaneGFFAffineInvariance_derived`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_7_2_derivedInputs5` is unchanged. -/
theorem closure_7_2_derivedInputs17
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    : ClusterTimeContinuityStmt.{u} :=
  HarmonicBalls.Closure.closure_7_2_derivedInputs5 (hL1 := hL1)
    (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) (hE3 := hE3) (hDG := hDG)
    (hAff := HarmonicBalls.WholePlaneGFFAffineInvariance_derived) (hCC := hCC)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hE := hE) (hN := hN)

/-- Binder-hygiene wrapper `closure_8_1_derivedInputs17` of the counted form `closure_8_1` (fp-phase2-derived-inputs-17, worker z7): the binders hE1, hAff, hW are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.WholePlaneGFFAffineInvariance_derived`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_8_1_derivedInputs5` is unchanged. -/
theorem closure_8_1_derivedInputs17
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    : BoundaryMeasureZeroOfCompactClusterStmt.{u} :=
  HarmonicBalls.Closure.closure_8_1_derivedInputs5 (hL1 := hL1)
    (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) (hE3 := hE3) (hDG := hDG)
    (hAff := HarmonicBalls.WholePlaneGFFAffineInvariance_derived) (hCC := hCC)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hE := hE) (hN := hN)

/-- Binder-hygiene wrapper `closure_9_2_derivedInputs17` of the counted form `closure_9_2` (fp-phase2-derived-inputs-17, worker z7): the binders hE1, hAff, hW are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.WholePlaneGFFAffineInvariance_derived`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_9_2_derivedInputs5` is unchanged. -/
theorem closure_9_2_derivedInputs17
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    : HarmonicBalls.S9c.SubharmonicBallUniquenessC51Stmt.{u} :=
  HarmonicBalls.Closure.closure_9_2_derivedInputs5 (hL1 := hL1)
    (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) (hE3 := hE3) (hDG := hDG)
    (hAff := HarmonicBalls.WholePlaneGFFAffineInvariance_derived) (hCC := hCC)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hE := hE) (hN := hN)

/-- Binder-hygiene wrapper `closure_10_7_derivedInputs17` of the counted form `closure_10_7` (fp-phase2-derived-inputs-17, worker z7): the binders hE1, hAff, hW are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.WholePlaneGFFAffineInvariance_derived`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_10_7_derivedInputs5` is unchanged. -/
theorem closure_10_7_derivedInputs17
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallComplementBoundaryJordanStmt.{u} :=
  HarmonicBalls.Closure.closure_10_7_derivedInputs5 (hL1 := hL1)
    (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived) (hE3 := hE3) (hDG := hDG)
    (hAff := HarmonicBalls.WholePlaneGFFAffineInvariance_derived) (hCC := hCC)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hE := hE) (hN := hN) (hTor := hTor)

/-- Binder-hygiene wrapper `closure_11_2_derivedInputs17` of the counted form `closure_11_2` (fp-phase2-derived-inputs-17, worker z7): the binders hW, hE1 are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_11_2_derivedInputs5` is unchanged. -/
theorem closure_11_2_derivedInputs17
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    : HarmonicBallNotLipschitzStmt.{u} :=
  HarmonicBalls.Closure.closure_11_2_derivedInputs5 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hN := hN) (hL1 := hL1) (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM)

/-- Binder-hygiene wrapper `closure_11_5_derivedInputs17` of the counted form `closure_11_5` (fp-phase2-derived-inputs-17, worker z7): the binders hW, hE1 are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_11_5_derivedInputs5` is unchanged. -/
theorem closure_11_5_derivedInputs17
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    : NoConeConditionStmt.{u} :=
  HarmonicBalls.Closure.closure_11_5_derivedInputs5 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hN := hN) (hL1 := hL1) (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM)

/-- Binder-hygiene wrapper `closure_11_6_derivedInputs17` of the counted form `closure_11_6` (fp-phase2-derived-inputs-17, worker z7): the binders hW, hE1 are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_11_6_derivedInputs5` is unchanged. -/
theorem closure_11_6_derivedInputs17
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : AnnulusMassBoundByHarmonicChainStmt.{u} :=
  HarmonicBalls.Closure.closure_11_6_derivedInputs5 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hN := hN) (hL1 := hL1) (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    (hE3 := hE3)

/-- Binder-hygiene wrapper `typicalPointManyGoodScales_closed_derivedInputs17` of the counted form `typicalPointManyGoodScales_closed` (fp-phase2-derived-inputs-17, worker z7): the binders hW, hE1 are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `typicalPointManyGoodScales_closed_derivedInputs5` is unchanged. -/
theorem typicalPointManyGoodScales_closed_derivedInputs17
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : TypicalPointManyGoodScalesStmt.{u} :=
  HarmonicBalls.Closure.typicalPointManyGoodScales_closed_derivedInputs5 (hDG := hDG)
    (hCC := hCC) (hE := hE)
    (hW := (fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hN := hN) (hL1 := hL1) (hE1 := HarmonicBalls.lqgMeasureOfProfileMeasurable_derived)
    (hE3 := hE3)

/-- Binder-hygiene wrapper `closure_11_9_derivedInputs17` of the counted form `closure_11_9` (fp-phase2-derived-inputs-17, worker z7): the binders hCM, hMass, hFD are removed and supplied by the binder-free derived theorems `HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived`, `HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived`, `HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_11_9_derivedInputs3` is unchanged. -/
theorem closure_11_9_derivedInputs17
    (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : SmallMetricDiameterLargeMassStmt.{u} :=
  HarmonicBalls.Closure.closure_11_9_derivedInputs3 (hCM := HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived)
    (hWSC := hWSC) (hMet := hMet)
    (hMass := HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived)
    (hShift := hShift) (hFD := HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived)
    (hAx := hAx) (hDC := hDC) (hCMT := hCMT) (hPos := hPos) (hSupM := hSupM) (hFin := hFin)
    (hM1 := hM1) (hmeasure := hmeasure)

/-- Binder-hygiene wrapper `closure_11_16_derivedInputs17` of the counted form `closure_11_16` (fp-phase2-derived-inputs-17, worker z7): the binders hWeyl, hCM, hMass, hFD are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived`, `HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived`, `HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_11_16_derivedInputs3` is unchanged. -/
theorem closure_11_16_derivedInputs17
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : PinchSecondEventFaithfulStmt.{u} :=
  HarmonicBalls.Closure.closure_11_16_derivedInputs3 (hAx := hAx) (hK1 := hK1)
    (hholder := hholder) (hEx := hEx)
    (hWeyl := (fun γ Ω _ P hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hNa0 := hNa0) (hNa := hNa)
    (hCM := HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived) (hWSC := hWSC)
    (hMet := hMet) (hExists := hExists)
    (hMass := HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived)
    (hShift := hShift) (hFD := HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived)
    (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hM1 := hM1)
    (hM := hM) (hDiam := hDiam) (hMk := hMk) (hmeasure := hmeasure)

/-- Binder-hygiene wrapper `closure_11_17_derivedInputs17` of the counted form `closure_11_17` (fp-phase2-derived-inputs-17, worker z7): the binders hWeyl, hCM, hMass, hFD, hN2 are removed and supplied by the binder-free derived theorems `HarmonicBalls.Section6.lqgMeasureWeylScaling`, `HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived`, `HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived`, `HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived`, `HarmonicBalls.weylScaledEuclidean_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `closure_11_17_derivedInputs3` is unchanged. -/
theorem closure_11_17_derivedInputs17
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hWSC : WeylScalingCompositionFrozen.{u})
    (hMet : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hShift : LQGMetricContinuousShiftFactI.{u})
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : PinchThirdEventFaithfulStmt.{u} :=
  HarmonicBalls.Closure.closure_11_17_derivedInputs3 (hAx := hAx) (hK1 := hK1)
    (hholder := hholder) (hEx := hEx)
    (hWeyl := (fun γ Ω _ P hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc))
    (hNa0 := hNa0) (hNa := hNa)
    (hCM := HarmonicBalls.DerivedInputs9.cameronMartinGFFMutualAbsCont_derived) (hWSC := hWSC)
    (hMet := hMet) (hExists := hExists)
    (hMass := HarmonicBalls.MassFunctionalDerived.lqgMassFunctionalMeasurable_derived)
    (hShift := hShift) (hFD := HarmonicBalls.planeDomainMinusConvexCompactPreconnected_derived)
    (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10) (hSupM := hSupM) (hFin := hFin) (hM1 := hM1)
    (hM := hM) (hDiam := hDiam) (hMk := hMk) (hN2 := HarmonicBalls.weylScaledEuclidean_derived)
    (hmeasure := hmeasure)

end HarmonicBalls.Closure

namespace HarmonicBalls.S11c

/-- Binder-hygiene wrapper `firstPass_11_10_derivedInputs17` of the counted form `firstPass_11_10` (fp-phase2-derived-inputs-17, worker z7): the binders hM2 are removed and supplied by the binder-free derived theorems `HarmonicBalls.weylShiftedMassMeasurable_derived` (DERIVED rows of docs/campaign/PHASE2-DERIVATION-STATUS.md). No binder is added and no conclusion is weakened. Original `firstPass_11_10_derivedInputs3` is unchanged. -/
theorem firstPass_11_10_derivedInputs17
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hFactI : LQGMetricContinuousShiftFactI.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : SmallMetricDiameterLargeMassSquareStmt.{u} :=
  HarmonicBalls.S11c.firstPass_11_10_derivedInputs3 (hDC := hDC) (hCM := hCM) (hPos := hPos)
    (hSupM := hSupM) (hFin := hFin) (hFactI := hFactI) (hM1 := hM1)
    (hM2 := HarmonicBalls.weylShiftedMassMeasurable_derived) (hAx := hAx) (hmeasure := hmeasure)

end HarmonicBalls.S11c
