import Lean
import HarmonicBalls.Proofs.Sec5.StagedInputAssembly

/-!
# Section 5 staged-input checks

Worker z4, task `section5-derived-staged-input-assembly`. Checks for the exports of
HarmonicBalls/Proofs/Sec5/StagedInputAssembly.lean:

* typed checks: each export has the expected binder types, in the stated order, and the frozen Draft conclusion. The
  expected binder types are restated here from the staged input statements of HarmonicBalls/Proposed/LQG.lean and
  from the open leaves `TypicalPointManyGoodScalesStmt` (Lemma 8.2) and `ClusterBoundaryTouchingRightContinuityStep` (G12);
* insertion scope: the all-insertion coordinate-change binder of results 5.5 and 5.7 is implicit in `Ω` and quantified
  over the insertion `α₀`; the insertion-zero binder of the other exports is explicit and fixes the insertion at `0`;
* axioms: each export depends only on `propext`, `Classical.choice` and `Quot.sound`;
* consumption: every binder occurs in the proof body (no decorative hypothesis).

Credit: Leonardo Bonanno, whose work is consumed through the imported modules, which carry his credit (see the header of
HarmonicBalls/Proofs/Sec5/StagedInputAssembly.lean).
-/

open Lean Meta MeasureTheory

namespace HarmonicBalls

universe u

/-! ## Expected binder types, restated from the staged input statements -/

abbrev expectedDG : Prop := ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc

abbrev expectedCC0 : Prop := ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc

abbrev expectedE : Prop := ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc

abbrev expectedCCall : Prop := ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc

/-! ## Typed checks -/

example : expectedDG.{u} → expectedCC0.{u} → expectedE.{u} → LQGVolumeGrowthAllScalesStmt.{u} :=
  volumeGrowthI2_of_staged_inputs

example : expectedDG.{u} → expectedCC0.{u} → expectedE.{u} → LiouvilleVolumeGrowthStmt.{u} :=
  liouvilleVolumeGrowth_of_staged_inputs

example : expectedDG.{u} → expectedCC0.{u} → expectedE.{u} → HarnackTypeEstimateStmt.{u} :=
  harnackTypeEstimate_of_staged_inputs

example : expectedDG.{u} → expectedCC0.{u} → expectedE.{u} → ClusterUpperBoundStmt.{u} :=
  section5_1_of_staged_inputs

example : expectedDG.{u} → expectedCC0.{u} → expectedE.{u} → TypicalPointManyGoodScalesStmt.{u} →
    ClusterBoundaryTouchingRightContinuityStep.{u} → ClusterContinuityStmt.{u} :=
  section5_2_of_staged_inputs

example : expectedDG.{u} → expectedCC0.{u} → expectedE.{u} → TypicalPointManyGoodScalesStmt.{u} →
    ClusterBoundaryMeasureZeroStmt.{u} :=
  section5_3_of_staged_inputs

example : expectedDG.{u} → expectedCC0.{u} → expectedE.{u} → TypicalPointManyGoodScalesStmt.{u} →
    RegularizedClusterHarmonicBallsStmt.{u} :=
  section5_4_of_staged_inputs

example : expectedDG.{u} → expectedCCall.{u} → expectedE.{u} → TypicalPointManyGoodScalesStmt.{u} →
    ExistenceHarmonicBallsStmt.{u} :=
  section5_5_of_staged_inputs

example : expectedDG.{u} → expectedCC0.{u} → expectedE.{u} → UniquenessHarmonicBallsStmt.{u} :=
  section5_6_of_staged_inputs

example : expectedDG.{u} → expectedCCall.{u} → expectedE.{u} → ClusterScaleInvarianceStmt.{u} :=
  section5_7_of_staged_inputs

example : expectedDG.{u} → expectedCC0.{u} → expectedE.{u} → ClusterStrongCompatibilityStmt.{u} :=
  section5_8_of_staged_inputs

example : expectedCCall.{u} → expectedCC0.{u} :=
  coordChange_zero_of_all_insertions

/-! ## Insertion scope, axioms and consumption -/

/-- The variables occurring in an expression. -/
def occursIn (x : FVarId) (e : Expr) : Bool :=
  (Expr.find? (fun t => t.isFVar && t.fvarId! == x) e).isSome

/-- Checks one export: standard axioms only; the coordinate-change binder (position `1`) is implicit in `Ω` exactly
when `allInsertions`; every binder of the proof occurs in its body. -/
def checkExport (n : Name) (nBinders : Nat) (allInsertions : Bool) : MetaM Unit := do
  let some ci := (← getEnv).find? n | throwError "missing declaration {n}"
  for a in ← collectAxioms n do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "{n} depends on the non-standard constant {a}"
  forallTelescope ci.type fun xs _ => do
    unless xs.size == nBinders do
      throwError "{n} has {xs.size} binders, expected {nBinders}"
    let t ← inferType xs[1]!
    let isImplicit := match t with
      | .forallE _ _ _ .implicit => true
      | _ => false
    unless isImplicit == allInsertions do
      throwError "{n}: the coordinate-change binder has the wrong insertion scope"
  let valOf : ConstantInfo → Option Expr := fun c => match c with
    | .defnInfo d => some d.value
    | .thmInfo d => some d.value
    | _ => none
  let some v := valOf ci | throwError "{n} has no value"
  lambdaTelescope v fun ys body => do
    for y in ys do
      unless occursIn y.fvarId! body do
        throwError "{n}: binder {y} does not occur in the proof body"

#eval show MetaM Unit from do
  checkExport ``volumeGrowthI2_of_staged_inputs 3 false
  checkExport ``liouvilleVolumeGrowth_of_staged_inputs 3 false
  checkExport ``harnackTypeEstimate_of_staged_inputs 3 false
  checkExport ``section5_1_of_staged_inputs 3 false
  checkExport ``section5_2_of_staged_inputs 5 false
  checkExport ``section5_3_of_staged_inputs 4 false
  checkExport ``section5_4_of_staged_inputs 4 false
  checkExport ``section5_6_of_staged_inputs 3 false
  checkExport ``section5_8_of_staged_inputs 3 false
  checkExport ``section5_5_of_staged_inputs 4 true
  checkExport ``section5_7_of_staged_inputs 3 true

#print axioms volumeGrowthI2_of_staged_inputs
#print axioms liouvilleVolumeGrowth_of_staged_inputs
#print axioms harnackTypeEstimate_of_staged_inputs
#print axioms section5_1_of_staged_inputs
#print axioms section5_2_of_staged_inputs
#print axioms section5_3_of_staged_inputs
#print axioms section5_4_of_staged_inputs
#print axioms section5_5_of_staged_inputs
#print axioms section5_6_of_staged_inputs
#print axioms section5_7_of_staged_inputs
#print axioms section5_8_of_staged_inputs
#print axioms coordChange_zero_of_all_insertions

end HarmonicBalls
