import HarmonicBalls.Proofs.Sec3.Assembly
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Section 3 from the four remaining literature inputs

Lemmas 3.1-3.5 at their frozen statements (`LeastSupersolutionMemStmt`, `ClusterOpenLaplacianStmt`,
`ClusterMonotoneStmt`, `ClusterConservationOfMassStmt`, `ClusterCompatibilityStmt`; `HarmonicBalls/Draft/Section3.lean`).

The existing exports of `HarmonicBalls/Proofs/Sec3/Assembly.lean` take six staged premises. This file discharges the
two premises that have proved providers and keeps four explicit:

* `hAff` (`WholePlaneGFFAffineInvariance`) is `wholePlaneGFFAffineInvariance_proved`
  (`HarmonicBalls/Proofs/Sec9/AffineInvarianceAssembly.lean`), derived from the frozen whole-plane GFF covariance.
* `hW` (`LQGMeasureWeylScaling`) is `HarmonicBalls.Section6.lqgMeasureWeylScaling`
  (`HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean`), derived from literal vague convergence.
* Explicit: `hDG` (`WholePlaneLQGBallMassBounds`, Ding-Gwynne 2020, Lemma 3.8), `hCC` (`LQGMeasureCoordChange`, Fact 2.1 IV),
  `hE` (`LQGMeasureExistence`, Section 2.2 of the paper) and `hN` (`LQGMeasureNonatomic`, Fact 2.1 I). They are staged in
  `HarmonicBalls/Proposed/LQG.lean` and remain pending operator source-check; this file does not certify them.

Both providers are instantiated universally at the carrier universe `u` (`wholePlaneGFFAffineInvariance_univ`,
`lqgMeasureWeylScaling_univ`) and passed to the existing exports. Input I2 (`LQGVolumeGrowthAllScalesStmt`) is produced
inside `lqgVolumeGrowthAllScalesStmt_of_literature`, so it is not a hypothesis of the exports here.

This is compilation evidence only. It is not closure of Lemmas 3.1-3.5; no frozen statement, staged premise or
existing export is edited. The guards at the end check the printed dependencies, the binder shapes of the exports,
and the constant closure of the two providers.

Credit: the LatticeProb library of Leonardo Bonanno is in the import closure of this module, reached through
`HarmonicBalls/Proofs/Sec9/AffineInvarianceAssembly.lean`. The constant closures of the two providers reach no
declaration of that library (guard below), and the import closure of `HarmonicBalls/Proofs/Sec3/Assembly.lean` contains
none of its modules, so the five exports use no declaration of that library.
-/

namespace HarmonicBalls

universe u

section DerivedInputs

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
  (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)

/-- Whole-plane GFF affine invariance at every carrier `Ω : Type u`, from `wholePlaneGFFAffineInvariance_proved`. -/
theorem wholePlaneGFFAffineInvariance_univ :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc :=
  fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc

/-- Weyl scaling of the LQG measures at every carrier `Ω : Type u` with `α₀ = 0`, from
`HarmonicBalls.Section6.lqgMeasureWeylScaling`. -/
theorem lqgMeasureWeylScaling_univ :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc :=
  fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc

include hDG hCC hE hN

/-- **Lemma 3.1** (lemma:basic-properties; Draft/Section3.lean:47) from the four remaining staged literature inputs. -/
theorem leastSupersolutionMem_of_remaining_literature : LeastSupersolutionMemStmt.{u} :=
  leastSupersolutionMem_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

/-- **Lemma 3.2** (lemma:non-coincidence-open-harmonic; Draft/Section3.lean:66) from the four remaining inputs. -/
theorem clusterOpenLaplacian_of_remaining_literature : ClusterOpenLaplacianStmt.{u} :=
  clusterOpenLaplacian_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

/-- **Lemma 3.3** (lemma:monotonicity; Draft/Section3.lean:89) from the four remaining inputs. -/
theorem clusterMonotone_of_remaining_literature : ClusterMonotoneStmt.{u} :=
  clusterMonotone_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

/-- **Lemma 3.4** (lemma:conservation-of-mass, correction C4; Draft/Section3.lean:102) from the four remaining inputs. -/
theorem clusterConservationOfMass_of_remaining_literature : ClusterConservationOfMassStmt.{u} :=
  clusterConservationOfMass_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

/-- **Lemma 3.5** (lemma:cluster-compatibility; Draft/Section3.lean:119) from the four remaining inputs. -/
theorem clusterCompatibility_of_remaining_literature : ClusterCompatibilityStmt.{u} :=
  clusterCompatibility_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

-- Typed examples at the exact frozen statements, with the four retained premises as the only hypotheses.
example : LeastSupersolutionMemStmt.{u} := leastSupersolutionMem_of_remaining_literature hDG hCC hE hN
example : ClusterOpenLaplacianStmt.{u} := clusterOpenLaplacian_of_remaining_literature hDG hCC hE hN
example : ClusterMonotoneStmt.{u} := clusterMonotone_of_remaining_literature hDG hCC hE hN
example : ClusterConservationOfMassStmt.{u} := clusterConservationOfMass_of_remaining_literature hDG hCC hE hN
example : ClusterCompatibilityStmt.{u} := clusterCompatibility_of_remaining_literature hDG hCC hE hN

end DerivedInputs

#check @leastSupersolutionMem_of_remaining_literature
#check @clusterOpenLaplacian_of_remaining_literature
#check @clusterMonotone_of_remaining_literature
#check @clusterConservationOfMass_of_remaining_literature
#check @clusterCompatibility_of_remaining_literature

#print axioms wholePlaneGFFAffineInvariance_univ
#print axioms lqgMeasureWeylScaling_univ
#print axioms leastSupersolutionMem_of_remaining_literature
#print axioms clusterOpenLaplacian_of_remaining_literature
#print axioms clusterMonotone_of_remaining_literature
#print axioms clusterConservationOfMass_of_remaining_literature
#print axioms clusterCompatibility_of_remaining_literature

-- Guards (an error fails the check): the five exports depend only on the standard constants, take exactly the four
-- retained premises and neither derived premise nor I2, and apply the two providers; the provider closure reaches no
-- Section 2 assembly, Section 3 or 4 declaration, and no theorem or opaque constant of Proposed or External.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let exps : Array Name := #[``leastSupersolutionMem_of_remaining_literature,
    ``clusterOpenLaplacian_of_remaining_literature, ``clusterMonotone_of_remaining_literature,
    ``clusterConservationOfMass_of_remaining_literature, ``clusterCompatibility_of_remaining_literature]
  let premises : Array Name := #[``WholePlaneLQGBallMassBounds, ``LQGMeasureCoordChange,
    ``LQGMeasureExistence, ``LQGMeasureNonatomic]
  let derived : Array Name := #[``WholePlaneGFFAffineInvariance, ``LQGMeasureWeylScaling,
    ``LQGVolumeGrowthAllScalesStmt]
  let providers : Array Name := #[``wholePlaneGFFAffineInvariance_univ, ``lqgMeasureWeylScaling_univ]
  let valOf : ConstantInfo → Option Expr := fun c => match c with
    | .thmInfo tv => some tv.value
    | .defnInfo dv => some dv.value
    | _ => none
  for e in exps do
    for a in (← liftCoreM (collectAxioms e)) do
      unless std.contains a do
        throwError "{e} depends on the non-standard constant {a}"
    let some ci := env.find? e | throwError "missing {e}"
    let some v := valOf ci | throwError "{e} has no value"
    let tys := ci.type.getUsedConstants
    for p in premises do
      unless tys.contains p do
        throwError "{e} lacks the retained premise {p}"
    for d in derived do
      if tys.contains d then
        throwError "{e} takes {d} as a hypothesis"
    for p in providers do
      unless v.getUsedConstants.contains p do
        throwError "{e} does not apply {p}"
  for p in providers do
    for a in (← liftCoreM (collectAxioms p)) do
      unless std.contains a do
        throwError "{p} depends on the non-standard constant {a}"
  let forbidden : List String := ["HarmonicBalls.Proofs.Sec3", "HarmonicBalls.Steps.Sec3",
    "HarmonicBalls.Proofs.Sec4", "HarmonicBalls.Steps.Sec4", "HarmonicBalls.Proofs.Sec2.Assembly"]
  let mut todo : Array Name := #[``HarmonicBalls.wholePlaneGFFAffineInvariance_proved,
    ``HarmonicBalls.Section6.lqgMeasureWeylScaling]
  let mut seen : NameSet := {}
  let mut hbCount : Nat := 0
  let mut propDefs : Nat := 0
  let mut auxNames : Array Name := #[]
  let mut latMods : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some mi := env.getModuleIdxFor? n | continue
    let md := env.header.moduleNames[mi]!
    if md.getRoot == `LatticeProb then
      latMods := latMods.insert md
    unless md.getRoot == `HarmonicBalls || md.getRoot == `LatticeProb do continue
    if forbidden.any (fun f => md.toString.startsWith f) then
      throwError "the affine or Weyl provider reaches {n} in {md}: circular dependency"
    let some ci := env.find? n | continue
    if md.toString.startsWith "HarmonicBalls.Proposed" || md.toString.startsWith "HarmonicBalls.External" then
      -- Allowed: the Prop-valued definitions (statements) and the proof obligations Lean abstracts out of a
      -- definition body (`_proof_k`). Any other constant there, in particular a theorem, is an error.
      let ofDef : Bool := match env.find? n.getPrefix with
        | some (.defnInfo _) => n.isInternalDetail
        | _ => false
      let isDef : Bool := match ci with
        | .defnInfo _ => true
        | _ => false
      unless ofDef || isDef do
        throwError "the provider closure reaches the non-definitional literature constant {n} in {md}"
      if ofDef then
        auxNames := auxNames.push n
      else
        propDefs := propDefs + 1
    if md.getRoot == `HarmonicBalls then
      hbCount := hbCount + 1
    todo := todo ++ ci.type.getUsedConstants
    if let some v := valOf ci then
      todo := todo ++ v.getUsedConstants
  let lat := (env.header.moduleNames.filter (fun m => m.getRoot == `LatticeProb)).size
  let auxStr := ", ".intercalate (auxNames.toList.map toString)
  let latStr := ", ".intercalate (latMods.toList.map toString)
  logInfo m!"DerivedInputAssembly: standard constants only for the five exports and the two providers; the exports take exactly the four retained premises and apply both providers; the provider closure reaches {hbCount} HarmonicBalls declarations, {propDefs} Proposed or External definitions and the auxiliary proofs [{auxStr}] of Proposed definitions; none in Sec2.Assembly, Sec3, Sec4; no Proposed or External theorem; LatticeProb modules reached by the two providers: [{latStr}]; LatticeProb modules in the import closure: {lat}"

end HarmonicBalls
