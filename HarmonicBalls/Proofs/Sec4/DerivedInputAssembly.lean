import HarmonicBalls.Proofs.Sec3.DerivedInputAssembly
import HarmonicBalls.Proofs.Sec4.ClusterLowerBound
import HarmonicBalls.Proofs.Sec4.LeastSupersolutionHolder
import HarmonicBalls.Proofs.Sec4.ClusterGreenIdentity
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Section 4 from the four remaining literature inputs

Proposition 4.1, Lemma 4.2 and Lemma 4.3 at their frozen statements (`ClusterLowerBoundStmt`,
`LeastSupersolutionHolderStmt`, `ClusterSubharmonicBallStmt`; `HarmonicBalls/Draft/Section4.lean:95`, `:116`, `:132`).

The existing exports `clusterLowerBound_of_literature` (`HarmonicBalls/Proofs/Sec4/ClusterLowerBound.lean`),
`leastSupersolutionHolder_of_literature` (`HarmonicBalls/Proofs/Sec4/LeastSupersolutionHolder.lean`) and
`clusterSubharmonicBall_of_literature` (`HarmonicBalls/Proofs/Sec4/ClusterGreenIdentity.lean`) take six staged premises.
This file discharges the two premises that have proved providers and keeps four explicit:

* `hAff` (`WholePlaneGFFAffineInvariance`) is `wholePlaneGFFAffineInvariance_univ`
  (`HarmonicBalls/Proofs/Sec3/DerivedInputAssembly.lean`), the carrier-universal form of `wholePlaneGFFAffineInvariance_proved`
  (`HarmonicBalls/Proofs/Sec9/AffineInvarianceAssembly.lean`); its binders are the carrier, measure and field data only,
  and it follows from the covariance characterization of the whole-plane field.
* `hW` (`LQGMeasureWeylScaling`) is `lqgMeasureWeylScaling_univ` (`HarmonicBalls/Proofs/Sec3/DerivedInputAssembly.lean`),
  the carrier-universal form of `HarmonicBalls.Section6.lqgMeasureWeylScaling` at `α₀ = 0`
  (`HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean`); its binders are the carrier, measure and field data only, and it
  follows from the vague-limit definition of the LQG measure.
* Explicit: `hDG` (`WholePlaneLQGBallMassBounds`, Ding-Gwynne 2020, Lemma 3.8), `hCC` (`LQGMeasureCoordChange`, Fact 2.1 IV),
  `hE` (`LQGMeasureExistence`, Section 2.2 of the paper) and `hN` (`LQGMeasureNonatomic`, Fact 2.1 I). They are staged in
  `HarmonicBalls/Proposed/LQG.lean` and remain pending source-check; this file does not certify them.

Input I2 (`LQGVolumeGrowthAllScalesStmt`) is produced inside `lqgVolumeGrowthAllScalesStmt_of_literature`, so it is not a
hypothesis of the exports here. Both providers are instantiated at the carrier universe `u`.

This is compilation evidence only. It is not closure of Proposition 4.1 or of Lemmas 4.2 and 4.3, and no frozen statement,
staged premise or existing export is edited. The guards at the end check the printed dependencies, the binder shapes of the
exports, and the constant closure of the two providers.

Credit: the LatticeProb library of Leonardo Bonanno is in the import closure of this module, through the two providers
(`HarmonicBalls/Proofs/Sec9/AffineInvarianceAssembly.lean` and `HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean`, which
credit him). The guard below reports the LatticeProb declarations reached by the constant closure of the two providers.
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

include hDG hCC hE hN

/-- **Proposition 4.1** (prop:lower-bound; `HarmonicBalls/Draft/Section4.lean:95`) from the four remaining staged inputs,
with the affine and Weyl premises discharged by `wholePlaneGFFAffineInvariance_univ` and `lqgMeasureWeylScaling_univ`. -/
theorem clusterLowerBound_of_remaining_literature : ClusterLowerBoundStmt.{u} :=
  clusterLowerBound_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

/-- **Lemma 4.2** (odometer:cont; `HarmonicBalls/Draft/Section4.lean:116`) from the four remaining staged inputs,
with the affine and Weyl premises discharged by `wholePlaneGFFAffineInvariance_univ` and `lqgMeasureWeylScaling_univ`. -/
theorem leastSupersolutionHolder_of_remaining_literature : LeastSupersolutionHolderStmt.{u} :=
  leastSupersolutionHolder_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

/-- **Lemma 4.3** (lemma:harmonic-ball; `HarmonicBalls/Draft/Section4.lean:132`) from the four remaining staged inputs,
with the affine and Weyl premises discharged by `wholePlaneGFFAffineInvariance_univ` and `lqgMeasureWeylScaling_univ`. -/
theorem clusterSubharmonicBall_of_remaining_literature : ClusterSubharmonicBallStmt.{u} :=
  clusterSubharmonicBall_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

-- Typed examples at the exact frozen statements, with the four retained premises as the only hypotheses.
example : ClusterLowerBoundStmt.{u} := clusterLowerBound_of_remaining_literature hDG hCC hE hN
example : LeastSupersolutionHolderStmt.{u} := leastSupersolutionHolder_of_remaining_literature hDG hCC hE hN
example : ClusterSubharmonicBallStmt.{u} := clusterSubharmonicBall_of_remaining_literature hDG hCC hE hN

end DerivedInputs

-- Guards (an error fails the check): the three exports depend only on the standard constants, take exactly the four
-- retained premises and neither derived premise nor I2, and apply the two providers; the provider closure reaches no
-- Section 2 assembly, Section 3 or 4 declaration, and no theorem or opaque constant of Proposed or External.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let exps : Array Name := #[``clusterLowerBound_of_remaining_literature,
    ``leastSupersolutionHolder_of_remaining_literature, ``clusterSubharmonicBall_of_remaining_literature]
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
  logInfo m!"Section4 DerivedInputAssembly: standard constants only for the three exports and the two providers; the exports take exactly the four retained premises and apply both providers; the provider closure reaches {hbCount} HarmonicBalls declarations, {propDefs} Proposed or External definitions and the auxiliary proofs [{auxStr}] of Proposed definitions; none in Sec2.Assembly, Sec3, Sec4; no Proposed or External theorem; LatticeProb modules reached by the two providers: [{latStr}]; LatticeProb modules in the import closure: {lat}"

end HarmonicBalls
