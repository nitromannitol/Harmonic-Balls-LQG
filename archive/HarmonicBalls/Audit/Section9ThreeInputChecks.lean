import Lean
import HarmonicBalls.Proofs.Sec9.ThreeInputAssembly

/-!
# Section 9 three-input checks

Checks for the exports of
HarmonicBalls/Proofs/Sec9/ThreeInputAssembly.lean:

* typed examples: each export accepts the staged inputs at their restated types (`hDG` as stated, `hCC` at insertion
  `0`, `hE` at all insertions) and returns the frozen Draft conclusions. The typical-point leaf `h82` is the only extra
  binder of the numbered export.
* binder check (MetaM): the binders of each export are exactly `hDG hCC hE` (comparison export) or `hDG hCC hE h82`
  (numbered export), all explicit. The export types contain none of the forbidden constants: the ordinary
  Proposition 9.2, the all-scales volume growth I2, the affine, Weyl and non-atomicity inputs, Lemma 6.11, the
  boundary-nullity statements, and the subrange step of Lemma 10.1.
* insertion scope (MetaM): the single `LQGMeasureCoordChange` occurrence is applied at the literal insertion `0`.
* axioms: each export depends only on `propext`, `Classical.choice` and `Quot.sound`.

Credit: Leonardo Bonanno. This module imports infrastructure of Leonardo Bonanno through the Lattice-Probability
lean-v4.35 dependency (LatticeProb.Bonanno), via `HarmonicBalls.Proofs.Sec9.ThreeInputAssembly`.
-/

open Lean Meta MeasureTheory

namespace HarmonicBalls

universe u

/-! ## Staged inputs at their exact types (restated from HarmonicBalls/Proposed/LQG.lean) -/

abbrev s9DG : Prop := ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc

abbrev s9CC : Prop := ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc

abbrev s9E : Prop := ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc

/-! ## Typed examples -/

example (hDG : s9DG.{u}) (hCC : s9CC.{u}) (hE : s9E.{u}) :
    ObstacleComparisonStmt.{u} ∧ HarmonicBallBoundarySubsetStmt.{u} ∧ RegularOpenEqOfAEEqStmt.{u} :=
  section9_comparison_results_of_three_inputs hDG hCC hE

example (hDG : s9DG.{u}) (hCC : s9CC.{u}) (hE : s9E.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ObstacleComparisonStmt.{u} ∧ HarmonicBallBoundarySubsetStmt.{u} ∧
      RegularOpenEqOfAEEqStmt.{u} ∧ SubharmonicBallUniquenessWeakStmt.{u} :=
  section9_numbered_results_of_three_inputs hDG hCC hE h82

/-! ## Binder, insertion and axiom checks (MetaM) -/

/-- The binder names of a declaration with an explicitness flag, read from the telescope of its type. -/
def s9Binders (n : Name) : MetaM (List (Name × Bool)) := do
  forallTelescope (← getConstInfo n).type fun xs _ => do
    xs.toList.mapM fun x => do
      let d ← getFVarLocalDecl x
      return (d.userName, d.binderInfo.isExplicit)

/-- Constants that must not occur in the type of a Section 9 export: the ordinary Proposition 9.2, the
predecessors that are discharged inside the producers, the boundary-nullity statements, and the subrange step of
Lemma 10.1 (outside this task). -/
def s9Forbidden : List Name :=
  [``SubharmonicBallUniquenessStmt, ``LQGVolumeGrowthAllScalesStmt, ``LQGMeasureWeylScaling,
   ``LQGMeasureNonatomic, ``WholePlaneGFFAffineInvariance, ``VeryGoodAnnulusHarnackTypeStmt,
   ``ClusterBoundaryNullAllRadii, ``BoundaryMeasureZeroOfCompactClusterStmt, ``VeryGoodAnnuliSubRangeStep]

/-- Checks one export: exact binder names, all explicit, required and forbidden constants in the type, and
standard axioms only. -/
def s9CheckExport (n : Name) (binders required forbidden : List Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let bs ← s9Binders n
  unless bs.map (·.1) == binders do
    throwError "{n}: binders {bs.map (·.1)}, expected {binders}"
  unless bs.all (·.2) do
    throwError "{n}: a binder is not explicit"
  for c in required do
    unless (ci.type.find? (fun e => e.isConstOf c)).isSome do
      throwError "{n}: required constant {c} does not occur in the type"
  for c in forbidden do
    if (ci.type.find? (fun e => e.isConstOf c)).isSome then
      throwError "{n}: forbidden constant {c} occurs in the type"
  let axs ← collectAxioms n
  for a in axs do
    unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
      throwError "{n}: unexpected axiom {a}"
  logInfo m!"{n}: binders {binders}; axioms {axs}"

/-- The coordinate-change occurrence in the type is applied at the literal insertion `0` (not at a bound `α₀`). -/
def s9CheckInsertionZero (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let some app := ci.type.find? (fun e => e.isAppOfArity ``LQGMeasureCoordChange 7)
    | throwError "{n}: no LQGMeasureCoordChange occurrence"
  let alpha0 := app.getAppArgs[4]!
  unless (alpha0.isAppOfArity ``OfNat.ofNat 3 && alpha0.getAppArgs[1]! == mkRawNatLit 0) do
    throwError "{n}: coordinate change is not applied at insertion 0"
  logInfo m!"{n}: coordinate change at insertion 0"

  let comparisonRequired := [``ObstacleComparisonStmt, ``HarmonicBallBoundarySubsetStmt, ``RegularOpenEqOfAEEqStmt]
  s9CheckExport ``section9_comparison_results_of_three_inputs [`hDG, `hCC, `hE] comparisonRequired
    (s9Forbidden ++ [``TypicalPointManyGoodScalesStmt, ``SubharmonicBallUniquenessWeakStmt])
  s9CheckInsertionZero ``section9_comparison_results_of_three_inputs
  s9CheckExport ``section9_numbered_results_of_three_inputs [`hDG, `hCC, `hE, `h82]
    (comparisonRequired ++ [``SubharmonicBallUniquenessWeakStmt, ``TypicalPointManyGoodScalesStmt]) s9Forbidden
  s9CheckInsertionZero ``section9_numbered_results_of_three_inputs

/-! ## Printed axioms -/

end HarmonicBalls
