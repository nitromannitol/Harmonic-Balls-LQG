import HarmonicBalls.Proofs.Sec3.Assembly
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Section 3 input consumption checks (Lemmas 3.1-3.5)

Independent type checks of the five assembled exports of `HarmonicBalls/Proofs/Sec3/Assembly.lean` against the
frozen statements of `HarmonicBalls/Draft/Section3.lean`: `LeastSupersolutionMemStmt` (Lemma 3.1),
`ClusterOpenLaplacianStmt` (Lemma 3.2), `ClusterMonotoneStmt` (Lemma 3.3), `ClusterConservationOfMassStmt`
(Lemma 3.4) and `ClusterCompatibilityStmt` (Lemma 3.5).

* The six staged literature premises of `HarmonicBalls/Proposed/LQG.lean` stay explicit hypotheses in the universe `u`
  of the exports: `hDG` (`WholePlaneLQGBallMassBounds`), `hAff` (`WholePlaneGFFAffineInvariance`), `hCC`
  (`LQGMeasureCoordChange`), `hW` (`LQGMeasureWeylScaling`), `hE` (`LQGMeasureExistence`), `hN`
  (`LQGMeasureNonatomic`). They are pending operator source-check; this file does not certify them.
* Input I2 (`LQGVolumeGrowthAllScalesStmt`, Draft/Section2.lean) is not a hypothesis of any export. Each export applies
  `lqgVolumeGrowthAllScalesStmt_of_literature` (`HarmonicBalls/Proofs/Sec2/Assembly.lean`) to the six premises and then
  its `_proved` lemma. The guards at the end check this on the constant graph.
* Each check is a typed `example` applying an export to the six premises; no standing-assumption package is introduced.
* No `LatticeProb.Bonanno` module is imported (checked by a guard below), so no Bonanno credit line is required here.
* This is compilation evidence only: it is not closure of Lemmas 3.1-3.5, and no frozen statement is edited.
-/

namespace HarmonicBalls

universe u

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
  (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)

include hDG hAff hCC hW hE hN

-- Lemma 3.1 (lemma:basic-properties; Draft/Section3.lean:47).
example : LeastSupersolutionMemStmt.{u} :=
  leastSupersolutionMem_of_literature hDG hAff hCC hW hE hN

-- Lemma 3.2 (lemma:non-coincidence-open-harmonic; Draft/Section3.lean:66).
example : ClusterOpenLaplacianStmt.{u} :=
  clusterOpenLaplacian_of_literature hDG hAff hCC hW hE hN

-- Lemma 3.3 (lemma:monotonicity; Draft/Section3.lean:89).
example : ClusterMonotoneStmt.{u} :=
  clusterMonotone_of_literature hDG hAff hCC hW hE hN

-- Lemma 3.4 (lemma:conservation-of-mass; Draft/Section3.lean:102).
example : ClusterConservationOfMassStmt.{u} :=
  clusterConservationOfMass_of_literature hDG hAff hCC hW hE hN

-- Lemma 3.5 (lemma:cluster-compatibility; Draft/Section3.lean:119).
example : ClusterCompatibilityStmt.{u} :=
  clusterCompatibility_of_literature hDG hAff hCC hW hE hN

#print axioms leastSupersolutionMem_of_literature
#print axioms clusterOpenLaplacian_of_literature
#print axioms clusterMonotone_of_literature
#print axioms clusterConservationOfMass_of_literature
#print axioms clusterCompatibility_of_literature

-- Guards (an error fails the check): standard axioms only; no LatticeProb module imported; each export's type has
-- the six premises and no I2 hypothesis; each export's value applies the I2 producer; the constant closure of the
-- I2 producer through HarmonicBalls declarations reaches no Section 3 or Section 4 declaration (no circularity).
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  if env.header.moduleNames.any (fun m => m.getRoot == `LatticeProb) then
    throwError "a LatticeProb module is imported: credit Leonardo Bonanno in this file"
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let exps : Array Name := #[``leastSupersolutionMem_of_literature, ``clusterOpenLaplacian_of_literature,
    ``clusterMonotone_of_literature, ``clusterConservationOfMass_of_literature,
    ``clusterCompatibility_of_literature]
  let premises : Array Name := #[``WholePlaneLQGBallMassBounds, ``WholePlaneGFFAffineInvariance,
    ``LQGMeasureCoordChange, ``LQGMeasureWeylScaling, ``LQGMeasureExistence, ``LQGMeasureNonatomic]
  let valOf : ConstantInfo → Option Expr := fun c => match c with
    | .thmInfo tv => some tv.value
    | .defnInfo dv => some dv.value
    | _ => none
  for e in exps do
    for a in (← liftCoreM (collectAxioms e)) do
      unless std.contains a do
        throwError "{e} depends on the non-standard axiom {a}"
    let some ci := env.find? e | throwError "missing {e}"
    let some v := valOf ci | throwError "{e} has no value"
    let tys := ci.type.getUsedConstants
    if tys.contains ``LQGVolumeGrowthAllScalesStmt then
      throwError "{e} takes I2 as a hypothesis"
    for p in premises do
      unless tys.contains p do
        throwError "{e} lacks the literature premise {p}"
    unless v.getUsedConstants.contains ``lqgVolumeGrowthAllScalesStmt_of_literature do
      throwError "{e} does not apply lqgVolumeGrowthAllScalesStmt_of_literature"
  let forbidden : List String := ["HarmonicBalls.Proofs.Sec3", "HarmonicBalls.Steps.Sec3",
    "HarmonicBalls.Draft.Section3", "HarmonicBalls.Proofs.Sec4", "HarmonicBalls.Steps.Sec4",
    "HarmonicBalls.Draft.Section4"]
  let mut todo : Array Name := #[``lqgVolumeGrowthAllScalesStmt_of_literature]
  let mut seen : NameSet := {}
  let mut hbCount : Nat := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some mi := env.getModuleIdxFor? n | continue
    let md := env.header.moduleNames[mi]!
    unless md.getRoot == `HarmonicBalls do continue
    if forbidden.any (fun f => md.toString.startsWith f) then
      throwError "the I2 producer reaches {n} in {md}: circular dependency"
    hbCount := hbCount + 1
    let some ci := env.find? n | continue
    todo := todo ++ ci.type.getUsedConstants
    if let some v := valOf ci then
      todo := todo ++ v.getUsedConstants
  logInfo m!"Section3InputChecks: standard axioms; no LatticeProb module; I2 is not a premise; six literature premises present; I2 consumed through lqgVolumeGrowthAllScalesStmt_of_literature; the I2 producer reaches {hbCount} HarmonicBalls declarations, none in Section 3 or 4"

end HarmonicBalls
