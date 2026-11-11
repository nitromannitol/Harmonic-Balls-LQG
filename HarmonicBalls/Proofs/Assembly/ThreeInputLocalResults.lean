import HarmonicBalls.Proofs.Sec9.WeakUniquenessDerivedInputs
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.Sec4.ClusterLowerBound
import HarmonicBalls.Proofs.Sec4.LeastSupersolutionHolder
import HarmonicBalls.Proofs.Sec4.ClusterGreenIdentity
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Lemmas 3.1-3.5, Proposition 4.1 and Lemmas 4.2-4.3 from the three staged measure inputs

Pure assembly: this module adds no mathematics.
It is a conditional reduction, not source-audited closure of any numbered result.

Exports. Eight theorems at the frozen statements of `HarmonicBalls/Draft/Section3.lean` and
`HarmonicBalls/Draft/Section4.lean`:

* `leastSupersolutionMem_of_three_staged_inputs`: Lemma 3.1, `LeastSupersolutionMemStmt` (Draft/Section3.lean:47);
* `clusterOpenLaplacian_of_three_staged_inputs`: Lemma 3.2, `ClusterOpenLaplacianStmt` (:66);
* `clusterMonotone_of_three_staged_inputs`: Lemma 3.3, `ClusterMonotoneStmt` (:89);
* `clusterConservationOfMass_of_three_staged_inputs`: Lemma 3.4, `ClusterConservationOfMassStmt` (:102);
* `clusterCompatibility_of_three_staged_inputs`: Lemma 3.5, `ClusterCompatibilityStmt` (:119);
* `clusterLowerBound_of_three_staged_inputs`: Proposition 4.1, `ClusterLowerBoundStmt` (Draft/Section4.lean:95);
* `leastSupersolutionHolder_of_three_staged_inputs`: Lemma 4.2, `LeastSupersolutionHolderStmt` (:116);
* `clusterSubharmonicBall_of_three_staged_inputs`: Lemma 4.3, `ClusterSubharmonicBallStmt` (:132).

Premises. Exactly three, in this order: `hDG` (`WholePlaneLQGBallMassBounds`, Ding-Gwynne Lemma 3.8), `hCC`
(`LQGMeasureCoordChange` at insertion `0`, Fact 2.1 IV) and `hE` (`LQGMeasureExistence` at EVERY insertion `α : ℝ`,
Section 2.2 of the paper). All three are staged in `HarmonicBalls/Proposed/LQG.lean` and remain pending
source-check. The quantifier over every insertion `α` in `hE` is kept as written; it is the premise of
`lqgVolumeGrowthAllScalesStmt_of_staged_inputs` (`HarmonicBalls/Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53`).

Premise strength, stated without shortcut. The four-premise exports of
`HarmonicBalls/Proofs/Sec3/DerivedInputAssembly.lean` and `HarmonicBalls/Proofs/Sec4/DerivedInputAssembly.lean` take
`hE` at insertion `0` only, and the nonatomicity premise `hN` at every insertion. Here `hN` is not a binder, the affine
and Weyl premises are proved providers, and `hE` is the all-insertion form. The all-insertion `hE` implies the
insertion-`0` instance. Whether it also yields the nonatomicity premise is the content of the I2 derivation
(`lqgVolumeGrowthAllScalesStmt_of_stronger_singularity`), which this file takes as written. The binder count alone
does not show that the two premise sets are equivalent or that one is weaker.

Derivation. Input I2 (`LQGVolumeGrowthAllScalesStmt`, Draft/Section2.lean:122) is
`lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE`, which applies
`lqgVolumeGrowthAllScalesStmt_of_stronger_singularity` (`HarmonicBalls/Proofs/Sec2/SingularAtomAtZero.lean:59`) with the
proved affine provider `wholePlaneGFFAffineInvariance_univ`. Each export is the corresponding `_proved` theorem applied
to I2: `leastSupersolutionMem_proved` (`Proofs/Sec3/Basic.lean:204`), `clusterOpenLaplacian_proved`
(`Proofs/Sec3/OpenLaplacian.lean:25`), `clusterMonotone_proved` (`Proofs/Sec3/Basic.lean:209`),
`clusterConservationOfMass_proved` (`Proofs/Sec3/ConservationOfMassLemma.lean:30`), `clusterCompatibility_proved`
(`Proofs/Sec3/ClusterCompatibility.lean:360`), `clusterLowerBound_proved` (`Proofs/Sec4/ClusterLowerBound.lean:18`),
`leastSupersolutionHolder_proved` (`Proofs/Sec4/LeastSupersolutionHolder.lean:19`) and `clusterSubharmonicBall_proved`
(`Proofs/Sec4/ClusterGreenIdentity.lean:261`). The mathematics inside those theorems is as written in their modules.
This file checks the Lean composition, the binders and the constant closure.

Not claimed. No numbered closure of Lemmas 3.1-3.5, Proposition 4.1 or Lemmas 4.2-4.3. No premise replaces a derived
target. No frozen statement, existing export, staged input or Proposed or External declaration is edited.

Credit: Leonardo Bonanno. The imported providers carry his credit for the Lattice-Probability infrastructure
(`LatticeProb`, Lattice-Probability lean-v4.35 dependency), as in `HarmonicBalls/Proofs/Sec9/WeakUniquenessDerivedInputs.lean`.
The guard at the end logs the `LatticeProb` modules reached by the eight exports; it does not forbid them.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

section ThreeStagedInputs

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)

include hDG hCC hE

/-- **Lemma 3.1** (lemma:basic-properties; `HarmonicBalls/Draft/Section3.lean:47`) from the three staged inputs. -/
theorem leastSupersolutionMem_of_three_staged_inputs : LeastSupersolutionMemStmt.{u} :=
  leastSupersolutionMem_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE)

/-- **Lemma 3.2** (lemma:non-coincidence-open-harmonic; `HarmonicBalls/Draft/Section3.lean:66`) from the three staged inputs. -/
theorem clusterOpenLaplacian_of_three_staged_inputs : ClusterOpenLaplacianStmt.{u} :=
  clusterOpenLaplacian_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE)

/-- **Lemma 3.3** (lemma:monotonicity; `HarmonicBalls/Draft/Section3.lean:89`) from the three staged inputs. -/
theorem clusterMonotone_of_three_staged_inputs : ClusterMonotoneStmt.{u} :=
  clusterMonotone_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE)

/-- **Lemma 3.4** (lemma:conservation-of-mass, correction C4; `HarmonicBalls/Draft/Section3.lean:102`) from the three
staged inputs. -/
theorem clusterConservationOfMass_of_three_staged_inputs : ClusterConservationOfMassStmt.{u} :=
  clusterConservationOfMass_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE)

/-- **Lemma 3.5** (lemma:cluster-compatibility; `HarmonicBalls/Draft/Section3.lean:119`) from the three staged inputs. -/
theorem clusterCompatibility_of_three_staged_inputs : ClusterCompatibilityStmt.{u} :=
  clusterCompatibility_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE)

/-- **Proposition 4.1** (prop:lower-bound; `HarmonicBalls/Draft/Section4.lean:95`) from the three staged inputs. -/
theorem clusterLowerBound_of_three_staged_inputs : ClusterLowerBoundStmt.{u} :=
  clusterLowerBound_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE)

/-- **Lemma 4.2** (odometer:cont; `HarmonicBalls/Draft/Section4.lean:116`) from the three staged inputs. -/
theorem leastSupersolutionHolder_of_three_staged_inputs : LeastSupersolutionHolderStmt.{u} :=
  leastSupersolutionHolder_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE)

/-- **Lemma 4.3** (lemma:harmonic-ball; `HarmonicBalls/Draft/Section4.lean:132`) from the three staged inputs. -/
theorem clusterSubharmonicBall_of_three_staged_inputs : ClusterSubharmonicBallStmt.{u} :=
  clusterSubharmonicBall_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE)

-- Typed examples at the frozen statements, with the three staged premises as the only hypotheses.
example : LeastSupersolutionMemStmt.{u} := leastSupersolutionMem_of_three_staged_inputs hDG hCC hE
example : ClusterOpenLaplacianStmt.{u} := clusterOpenLaplacian_of_three_staged_inputs hDG hCC hE
example : ClusterMonotoneStmt.{u} := clusterMonotone_of_three_staged_inputs hDG hCC hE
example : ClusterConservationOfMassStmt.{u} := clusterConservationOfMass_of_three_staged_inputs hDG hCC hE
example : ClusterCompatibilityStmt.{u} := clusterCompatibility_of_three_staged_inputs hDG hCC hE
example : ClusterLowerBoundStmt.{u} := clusterLowerBound_of_three_staged_inputs hDG hCC hE
example : LeastSupersolutionHolderStmt.{u} := leastSupersolutionHolder_of_three_staged_inputs hDG hCC hE
example : ClusterSubharmonicBallStmt.{u} := clusterSubharmonicBall_of_three_staged_inputs hDG hCC hE

end ThreeStagedInputs


-- Guard: standard axioms only; binder shape of each export (hDG, hCC, hE, frozen conclusion); the hE binder is the
-- all-insertion form and equals the premise of the staged I2 export; closure of the exports reaches no theorem that
-- proves Lemma 8.2 (the open obligation) and no non-definitional Proposed or External constant.
open Lean Meta Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let exports : Array Name := #[``HarmonicBalls.leastSupersolutionMem_of_three_staged_inputs,
    ``HarmonicBalls.clusterOpenLaplacian_of_three_staged_inputs,
    ``HarmonicBalls.clusterMonotone_of_three_staged_inputs,
    ``HarmonicBalls.clusterConservationOfMass_of_three_staged_inputs,
    ``HarmonicBalls.clusterCompatibility_of_three_staged_inputs,
    ``HarmonicBalls.clusterLowerBound_of_three_staged_inputs,
    ``HarmonicBalls.leastSupersolutionHolder_of_three_staged_inputs,
    ``HarmonicBalls.clusterSubharmonicBall_of_three_staged_inputs]
  let concls : Array Name := #[``HarmonicBalls.LeastSupersolutionMemStmt,
    ``HarmonicBalls.ClusterOpenLaplacianStmt, ``HarmonicBalls.ClusterMonotoneStmt,
    ``HarmonicBalls.ClusterConservationOfMassStmt, ``HarmonicBalls.ClusterCompatibilityStmt,
    ``HarmonicBalls.ClusterLowerBoundStmt, ``HarmonicBalls.LeastSupersolutionHolderStmt,
    ``HarmonicBalls.ClusterSubharmonicBallStmt]
  for p in exports do
    for a in (← liftCoreM (collectAxioms p)) do
      unless std.contains a do
        throwError "{p} depends on the non-standard constant {a}"
  -- Leading foralls of a type as (binder name, binder domain); head constant of a domain or conclusion.
  let binders : Expr → Array (String × Expr) := fun e => Id.run do
    let mut out : Array (String × Expr) := #[]
    let mut t := e
    while t.isForall do
      out := out.push (t.bindingName!.toString, t.bindingDomain!)
      t := t.bindingBody!
    return out
  let headOf : Expr → String := fun e =>
    ((e.getForallBody.getAppFn.constName?).map toString).getD "?"
  let some ref := env.find? ``HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_staged_inputs
    | throwError "the staged I2 export is missing"
  let refB := binders ref.type
  let expectedHeads : Array String := #["HarmonicBalls.WholePlaneLQGBallMassBounds",
    "HarmonicBalls.LQGMeasureCoordChange", "HarmonicBalls.LQGMeasureExistence"]
  for i in [0:exports.size] do
    let p := exports[i]!
    let some ci := env.find? p | throwError "export missing: {p}"
    let bs := binders ci.type
    unless bs.map (·.1) == #["hDG", "hCC", "hE"] do
      throwError "{p}: binders {bs.map (·.1)} differ from hDG hCC hE"
    for j in [0:3] do
      unless bs[j]!.2 == refB[j]!.2 do
        throwError "{p}: premise {bs[j]!.1} differs from the premise of lqgVolumeGrowthAllScalesStmt_of_staged_inputs"
    let heads := bs.map (fun b => headOf b.2)
    unless heads == expectedHeads do
      throwError "{p}: premise heads {heads} differ from the three staged Props"
    let hEb := binders bs[2]!.2
    unless hEb.size == 7 && hEb[4]!.1 == "α" do
      throwError "{p}: premise hE does not quantify over every insertion α"
    unless ci.type.getForallBody.getAppFn.constName? == some concls[i]! do
      throwError "{p}: conclusion differs from {concls[i]!}"
  -- Closure of the eight exports.
  let valOf : ConstantInfo → Option Expr := fun c => match c with
    | .defnInfo v => some v.value
    | .thmInfo v => some v.value
    | _ => none
  let mut todo : Array Name := #[]
  let mut parent : NameMap Name := {}
  for p in exports do
    if let some c := env.find? p then
      for k in c.type.getUsedConstants ++ ((valOf c).map (·.getUsedConstants)).getD #[] do
        unless parent.contains k do
          parent := parent.insert k p
          todo := todo.push k
  let mut seen : NameSet := {}
  let mut hbCount : Nat := 0
  let mut thmCount : Nat := 0
  let mut hbMods : NameSet := {}
  let mut propDefs : Array Name := #[]
  let mut auxNames : Array Name := #[]
  let mut latMods : NameSet := {}
  let mut sec4Count : Nat := 0
  let mut sec10Count : Nat := 0
  let mut sec9Weak : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some mi := env.getModuleIdxFor? n | continue
    let md := env.header.moduleNames[mi]!
    unless md.getRoot == `HarmonicBalls || md.getRoot == `LatticeProb do continue
    if md.getRoot == `LatticeProb then
      latMods := latMods.insert md
    let some c := env.find? n | continue
    let mdS := md.toString
    if md.getRoot == `HarmonicBalls then
      hbCount := hbCount + 1
      hbMods := hbMods.insert md
    if mdS.startsWith "HarmonicBalls.Proposed" || mdS.startsWith "HarmonicBalls.External" then
      -- Allowed: Prop-valued definitions and the `_proof_k` obligations Lean abstracts out of a definition body.
      let ofDef : Bool := match env.find? n.getPrefix with
        | some (.defnInfo _) => n.isInternalDetail
        | _ => false
      let isDef : Bool := match c with
        | .defnInfo _ => true
        | _ => false
      unless ofDef || isDef do
        throwError "the export reaches the non-definitional literature constant {n} in {md}"
      if ofDef then
        auxNames := auxNames.push n
      else
        propDefs := propDefs.push n
    if mdS.startsWith "HarmonicBalls.Proofs.Sec4" then
      sec4Count := sec4Count + 1
    if mdS.startsWith "HarmonicBalls.Proofs.Sec10" then
      sec10Count := sec10Count + 1
    if let .thmInfo _ := c then
      thmCount := thmCount + 1
      let concl := c.type.getForallBody.getAppFn.constName?
      if concl == some ``HarmonicBalls.TypicalPointManyGoodScalesStmt then
        throwError "{n} proves the open Lemma 8.2 obligation: the exports must not reach it"
      if concl == some ``HarmonicBalls.SubharmonicBallUniquenessWeakStmt then
        sec9Weak := sec9Weak.push n
    let mut kids : Array Name := c.type.getUsedConstants
    if let some v := valOf c then
      kids := kids ++ v.getUsedConstants
    for k in kids do
      unless parent.contains k do
        parent := parent.insert k n
        todo := todo.push k
  logInfo m!"ThreeInputLocalResults: standard axioms only for the eight exports; each export takes exactly hDG hCC hE; hE quantifies over every insertion α and equals the premise of lqgVolumeGrowthAllScalesStmt_of_staged_inputs; conclusions are the frozen Stmts"
  logInfo m!"closure: {hbCount} HarmonicBalls declarations ({thmCount} theorems) in {hbMods.size} modules; Proposed/External Props reached: {propDefs.toList}; aux obligations: {auxNames.toList}; LatticeProb modules: {latMods.size}"
  logInfo m!"LatticeProb modules reached: {latMods.toList}"
  logInfo m!"Section 4 declarations reached: {sec4Count}; Section 10 declarations reached: {sec10Count}; theorems concluding SubharmonicBallUniquenessWeakStmt reached: {sec9Weak.toList}"

end HarmonicBalls
