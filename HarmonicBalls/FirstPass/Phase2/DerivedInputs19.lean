import HarmonicBalls.FirstPass.Phase2.DerivedInputs17
import HarmonicBalls.FirstPass.Phase2.DerivedInputs15
import HarmonicBalls.FirstPass.Phase2.InnerMeasurableDerived
import HarmonicBalls.FirstPass.Closure.Sec6
import HarmonicBalls.Proposed.LQG

/-! Trade wrappers.
Scope: the DerivedInputs17 wrappers (counted results outside the DerivedInputs15 family). Trades:
(a) the binder `LQGMeasureNonatomic` (Proposed/LQG.lean:86) is discharged by
`HarmonicBalls.lqgMeasureNonatomicAll_of_inputs` (DerivedInputs15.lean:57) from the wrapper's own binders
`hDG`, `hCC` (specialised to alpha_0 = 0) and `hE`;
(b) the binder `LQGInternalDiamInnerMeasurableFrozen` is discharged by `HarmonicBalls.lqgInternalDiamInnerMeasurable_derived`
(InnerMeasurableDerived.lean:78) from the TRUE Proposed input `LQGMetricFieldAxioms` (Proposed/LQG.lean:225), which replaces it;
(d) the binder `VeryGoodAnnulusProbabilityStmt` is discharged by `HarmonicBalls.Closure.closure_6_7`
(FirstPass/Closure/Sec6.lean:57) from `hDG`, `hCC`, `hE`, where `hDG` is the TRUE Proposed input `WholePlaneLQGBallMassBounds`
that replaces it together with the nonatomic binder. No binder is added except these replacements; no FROZEN or Stmt binder is
added. Originals are unchanged. -/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- Trade wrapper `firstPass_8_2_S8d_noWeyl_derivedInputs19` of the counted form `firstPass_8_2_S8d_noWeyl`: the binders hL67, hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input (replacement binder hDG). Built on the DI17 wrapper `firstPass_8_2_S8d_noWeyl_derivedInputs17`, which is unchanged. -/
theorem firstPass_8_2_S8d_noWeyl_derivedInputs19
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : TypicalPointManyGoodScalesStmt.{u} :=
  HarmonicBalls.firstPass_8_2_S8d_noWeyl_derivedInputs17 (hL1 := hL1) (hfull := hfull)
    (hL67 := (HarmonicBalls.Closure.closure_6_7 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hEx))
    (hEx := hEx)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hEx γ α Ω P hC hcirc))
    (hCC := hCC) (hE3 := hE3)

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- Trade wrapper `closure_1_1_derivedInputs19` of the counted form `closure_1_1`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_1_1_derivedInputs17`, which is unchanged. -/
theorem closure_1_1_derivedInputs19
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : ExistenceUniquenessHarmonicBallsStmt.{u} :=
  HarmonicBalls.Closure.closure_1_1_derivedInputs17 (hL1 := hL1) (hE3 := hE3) (hDG := hDG)
    (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))

/-- Trade wrapper `closure_1_3_derivedInputs19` of the counted form `closure_1_3`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_1_3_derivedInputs17`, which is unchanged. -/
theorem closure_1_3_derivedInputs19
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
    : HarmonicBallLocalSetStmt.{u} :=
  HarmonicBalls.Closure.closure_1_3_derivedInputs17 (hmeasure := hmeasure) (hL1 := hL1)
    (hE3 := hE3) (hDG := hDG) (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))

/-- Trade wrapper `closure_5_2_derivedInputs19` of the counted form `closure_5_2`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_5_2_derivedInputs17`, which is unchanged. -/
theorem closure_5_2_derivedInputs19
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : ClusterContinuityStmt.{u} :=
  HarmonicBalls.Closure.closure_5_2_derivedInputs17 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))
    (hL1 := hL1) (hE3 := hE3)

/-- Trade wrapper `closure_5_3_derivedInputs19` of the counted form `closure_5_3`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_5_3_derivedInputs17`, which is unchanged. -/
theorem closure_5_3_derivedInputs19
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : ClusterBoundaryMeasureZeroStmt.{u} :=
  HarmonicBalls.Closure.closure_5_3_derivedInputs17 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))
    (hL1 := hL1) (hE3 := hE3)

/-- Trade wrapper `closure_5_4_derivedInputs19` of the counted form `closure_5_4`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_5_4_derivedInputs17`, which is unchanged. -/
theorem closure_5_4_derivedInputs19
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : RegularizedClusterHarmonicBallsStmt.{u} :=
  HarmonicBalls.Closure.closure_5_4_derivedInputs17 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))
    (hL1 := hL1) (hE3 := hE3)

/-- Trade wrapper `closure_5_5_derivedInputs19` of the counted form `closure_5_5`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_5_5_derivedInputs17`, which is unchanged. -/
theorem closure_5_5_derivedInputs19
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : ExistenceHarmonicBallsStmt.{u} :=
  HarmonicBalls.Closure.closure_5_5_derivedInputs17 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))
    (hL1 := hL1) (hE3 := hE3)

/-- Trade wrapper `closure_7_2_derivedInputs19` of the counted form `closure_7_2`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_7_2_derivedInputs17`, which is unchanged. -/
theorem closure_7_2_derivedInputs19
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : ClusterTimeContinuityStmt.{u} :=
  HarmonicBalls.Closure.closure_7_2_derivedInputs17 (hL1 := hL1) (hE3 := hE3) (hDG := hDG)
    (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))

/-- Trade wrapper `closure_8_1_derivedInputs19` of the counted form `closure_8_1`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_8_1_derivedInputs17`, which is unchanged. -/
theorem closure_8_1_derivedInputs19
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : BoundaryMeasureZeroOfCompactClusterStmt.{u} :=
  HarmonicBalls.Closure.closure_8_1_derivedInputs17 (hL1 := hL1) (hE3 := hE3) (hDG := hDG)
    (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))

/-- Trade wrapper `closure_9_2_derivedInputs19` of the counted form `closure_9_2`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_9_2_derivedInputs17`, which is unchanged. -/
theorem closure_9_2_derivedInputs19
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    : HarmonicBalls.S9c.SubharmonicBallUniquenessC51Stmt.{u} :=
  HarmonicBalls.Closure.closure_9_2_derivedInputs17 (hL1 := hL1) (hE3 := hE3) (hDG := hDG)
    (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))

/-- Trade wrapper `closure_10_7_derivedInputs19` of the counted form `closure_10_7`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_10_7_derivedInputs17`, which is unchanged. -/
theorem closure_10_7_derivedInputs19
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hTor : TorhorstSimpleLoopFrozen)
    : HarmonicBallComplementBoundaryJordanStmt.{u} :=
  HarmonicBalls.Closure.closure_10_7_derivedInputs17 (hL1 := hL1) (hE3 := hE3) (hDG := hDG)
    (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))
    (hTor := hTor)

/-- Trade wrapper `closure_11_2_derivedInputs19` of the counted form `closure_11_2`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_11_2_derivedInputs17`, which is unchanged. -/
theorem closure_11_2_derivedInputs19
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    : HarmonicBallNotLipschitzStmt.{u} :=
  HarmonicBalls.Closure.closure_11_2_derivedInputs17 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))
    (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM)

/-- Trade wrapper `closure_11_5_derivedInputs19` of the counted form `closure_11_5`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_11_5_derivedInputs17`, which is unchanged. -/
theorem closure_11_5_derivedInputs19
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    : NoConeConditionStmt.{u} :=
  HarmonicBalls.Closure.closure_11_5_derivedInputs17 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))
    (hL1 := hL1) (hE3 := hE3) (hCamp := hCamp) (hDec := hDec) (hCM := hCM)

/-- Trade wrapper `closure_11_6_derivedInputs19` of the counted form `closure_11_6`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `closure_11_6_derivedInputs17`, which is unchanged. -/
theorem closure_11_6_derivedInputs19
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : AnnulusMassBoundByHarmonicChainStmt.{u} :=
  HarmonicBalls.Closure.closure_11_6_derivedInputs17 (hDG := hDG) (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))
    (hL1 := hL1) (hE3 := hE3)

/-- Trade wrapper `typicalPointManyGoodScales_closed_derivedInputs19` of the counted form `typicalPointManyGoodScales_closed`: the binders hN are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input. Built on the DI17 wrapper `typicalPointManyGoodScales_closed_derivedInputs17`, which is unchanged. -/
theorem typicalPointManyGoodScales_closed_derivedInputs19
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    : TypicalPointManyGoodScalesStmt.{u} :=
  HarmonicBalls.Closure.typicalPointManyGoodScales_closed_derivedInputs17 (hDG := hDG)
    (hCC := hCC) (hE := hE)
    (hN := (fun Ω _ P γ α hC hcirc => HarmonicBalls.lqgMeasureNonatomicAll_of_inputs hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE γ α Ω P hC hcirc))
    (hL1 := hL1) (hE3 := hE3)

/-- Trade wrapper `closure_11_16_derivedInputs19` of the counted form `closure_11_16`: the binders hDiam are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input (replacement binder hFA). Built on the DI17 wrapper `closure_11_16_derivedInputs17`, which is unchanged. -/
theorem closure_11_16_derivedInputs19
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
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : PinchSecondEventFaithfulStmt.{u} :=
  HarmonicBalls.Closure.closure_11_16_derivedInputs17 (hAx := hAx) (hK1 := hK1)
    (hholder := hholder) (hEx := hEx) (hNa0 := hNa0) (hNa := hNa) (hWSC := hWSC) (hMet := hMet)
    (hExists := hExists) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10)
    (hSupM := hSupM) (hFin := hFin) (hM1 := hM1) (hM := hM)
    (hDiam := (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived hFA)) (hMk := hMk)
    (hmeasure := hmeasure)

/-- Trade wrapper `closure_11_17_derivedInputs19` of the counted form `closure_11_17`: the binders hDiam are discharged from the binders the wrapper keeps, binder-free derived theorems or the TRUE Proposed input (replacement binder hFA). Built on the DI17 wrapper `closure_11_17_derivedInputs17`, which is unchanged. -/
theorem closure_11_17_derivedInputs19
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
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc)
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.LQGMeasureLocality P γ α₀ hC hcirc)
    : PinchThirdEventFaithfulStmt.{u} :=
  HarmonicBalls.Closure.closure_11_17_derivedInputs17 (hAx := hAx) (hK1 := hK1)
    (hholder := hholder) (hEx := hEx) (hNa0 := hNa0) (hNa := hNa) (hWSC := hWSC) (hMet := hMet)
    (hExists := hExists) (hShift := hShift) (hDC := hDC) (hCMT := hCMT) (hPos10 := hPos10)
    (hSupM := hSupM) (hFin := hFin) (hM1 := hM1) (hM := hM)
    (hDiam := (HarmonicBalls.lqgInternalDiamInnerMeasurable_derived hFA)) (hMk := hMk)
    (hmeasure := hmeasure)

end HarmonicBalls.Closure
