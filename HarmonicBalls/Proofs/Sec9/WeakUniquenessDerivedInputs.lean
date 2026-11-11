import HarmonicBalls.Proofs.Sec2.SingularAtomAtZero
import HarmonicBalls.Proofs.Sec3.DerivedInputAssembly
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Weak Proposition 9.2 from the staged measure inputs and the open Lemma 8.2

This module is a reduction. It is not numbered
closure of Proposition 9.2, of Lemma 8.2 or of Input I2.

Export. `subharmonicBallUniquenessWeak_of_stronger_singularity_typicalScales` has the frozen conclusion
`SubharmonicBallUniquenessWeakStmt` (`HarmonicBalls/Draft/Section9.lean:125`, the weak form of Proposition 9.2, [C10]).
Its premises are exactly four:

* `hDG`, `hCC`, `hE`: the staged measure inputs `WholePlaneLQGBallMassBounds` (Ding-Gwynne, Lemma 3.8),
  `LQGMeasureCoordChange` at insertion `0` (Fact 2.1 IV) and `LQGMeasureExistence` at every insertion `α`.
  They are staged in `HarmonicBalls/Proposed/LQG.lean` and remain pending operator source-check.
* `h82 : TypicalPointManyGoodScalesStmt` (Lemma 8.2, `HarmonicBalls/Draft/Section8.lean:74`,
  lemma:mu_h-doubling-and-harnack). It is OPEN. It is kept as the frozen binder and is the derived proof
  obligation of this reduction.

Derived, not premises:

* Input I2, `LQGVolumeGrowthAllScalesStmt` (`HarmonicBalls/Draft/Section2.lean:122`), is
  `lqgVolumeGrowthAllScalesStmt_of_stronger_singularity` (`HarmonicBalls/Proofs/Sec2/SingularAtomAtZero.lean:59`)
  applied to `hDG`, `hAff`, `hCC`, `hE`; see `lqgVolumeGrowthAllScalesStmt_of_staged_inputs` below.
* `hAff`, `WholePlaneGFFAffineInvariance`, is `wholePlaneGFFAffineInvariance_univ`
  (`HarmonicBalls/Proofs/Sec3/DerivedInputAssembly.lean:55`), the carrier-universal form of
  `wholePlaneGFFAffineInvariance_proved` (`HarmonicBalls/Proofs/Sec9/AffineInvarianceAssembly.lean:21`).
* The step from I2 and Lemma 8.2 to the weak Proposition 9.2 is
  `subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales`
  (`HarmonicBalls/Proofs/Sec9/AffineInvarianceAssembly.lean:30`).

The frozen statements are used unchanged: carriers `Ω : Type u`, the outer `∀ᵐ ω ∂P`, and the quantifier order inside
`SubharmonicBallUniquenessWeakStmt` are inherited from `HarmonicBalls/Draft/Section9.lean`.

Credit: Leonardo Bonanno. The imported providers carry his credit for the Lattice-Probability infrastructure
(`LatticeProb.Bonanno`, Lattice-Probability lean-v4.35 dependency), as `HarmonicBalls/Proofs/Sec9/AffineInvarianceAssembly.lean`
states. The guard below finds no `LatticeProb` declaration in the closure of the exports. This is a credit only. It is
not a source admission, and no staged input is certified by this module.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Input I2 (`LQGVolumeGrowthAllScalesStmt`) from the staged measure inputs `hDG`, `hCC`, `hE`. The affine-invariance
premise of `lqgVolumeGrowthAllScalesStmt_of_stronger_singularity` is discharged by `wholePlaneGFFAffineInvariance_univ`,
so it is not a hypothesis here. Credit: Leonardo Bonanno (module header). -/
theorem lqgVolumeGrowthAllScalesStmt_of_staged_inputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    LQGVolumeGrowthAllScalesStmt.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_stronger_singularity hDG wholePlaneGFFAffineInvariance_univ hCC hE

/-- Weak Proposition 9.2 (`SubharmonicBallUniquenessWeakStmt`, frozen) from the staged measure inputs `hDG`, `hCC`, `hE`
and the open Lemma 8.2 binder `h82`. Affine invariance is discharged and I2 is derived. This is a reduction, not
numbered closure. Credit: Leonardo Bonanno (module header). -/
theorem subharmonicBallUniquenessWeak_of_stronger_singularity_typicalScales
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales
    (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE) h82

end HarmonicBalls

/-! ## Guards: printed axioms, binder shape and the provider closure -/

#check @HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_staged_inputs
#check @HarmonicBalls.subharmonicBallUniquenessWeak_of_stronger_singularity_typicalScales
open Lean Meta Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let exports : Array Name := #[``HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_staged_inputs,
    ``HarmonicBalls.subharmonicBallUniquenessWeak_of_stronger_singularity_typicalScales]
  for p in exports do
    for a in (← liftCoreM (collectAxioms p)) do
      unless std.contains a do
        throwError "{p} depends on the non-standard constant {a}"
  -- Binder shape of the export: premise names with the head constant of each premise type, and the conclusion head.
  let some ci := env.find? ``HarmonicBalls.subharmonicBallUniquenessWeak_of_stronger_singularity_typicalScales
    | throwError "export missing"
  let shape ← liftTermElabM <| forallTelescope ci.type fun xs body => do
    let mut out : Array String := #[]
    for x in xs do
      let nm ← x.fvarId!.getUserName
      let ty ← inferType x
      let head ← forallTelescope ty fun _ b => pure ((b.getAppFn.constName?.map toString).getD "?")
      out := out.push s!"{nm}:{head}"
    pure (out.push s!"concl:{(body.getAppFn.constName?.map toString).getD "?"}")
  logInfo m!"binder shape: {shape}"
  let expected : Array String := #["hDG:HarmonicBalls.WholePlaneLQGBallMassBounds",
    "hCC:HarmonicBalls.LQGMeasureCoordChange", "hE:HarmonicBalls.LQGMeasureExistence",
    "h82:HarmonicBalls.TypicalPointManyGoodScalesStmt",
    "concl:HarmonicBalls.SubharmonicBallUniquenessWeakStmt"]
  unless shape == expected do
    throwError "binder shape differs from the frozen export: {shape}"
  -- Closure of the two exports. Forbidden: the three numbered Section 4 result modules (theorems), any theorem
  -- concluding in a Section 4 statement or in Lemma 8.2. Watched and logged: other Section 4 declarations.
  let valOf : ConstantInfo → Option Expr := fun c => match c with
    | .defnInfo v => some v.value
    | .thmInfo v => some v.value
    | _ => none
  let sec4Modules : List String := ["HarmonicBalls.Proofs.Sec4.ClusterLowerBound",
    "HarmonicBalls.Proofs.Sec4.LeastSupersolutionHolder", "HarmonicBalls.Proofs.Sec4.ClusterGreenIdentity",
    "HarmonicBalls.Proofs.Sec4.DerivedInputAssembly"]
  let forbiddenConcl : List Name := [``HarmonicBalls.ClusterLowerBoundStmt,
    ``HarmonicBalls.LeastSupersolutionHolderStmt, ``HarmonicBalls.ClusterSubharmonicBallStmt,
    ``HarmonicBalls.TypicalPointManyGoodScalesStmt]
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
  let mut watched : Array String := #[]
  let mut i2Producers : Array Name := #[]
  let mut i2Binders : Array Name := #[]
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
    if mdS.startsWith "HarmonicBalls.Proofs.Sec4" || mdS.startsWith "HarmonicBalls.Steps.Sec4" ||
        mdS.startsWith "HarmonicBalls.Proofs.Sec10" then
      watched := watched.push s!"{n} <- {(parent.find? n).getD n}"
    if sec4Modules.contains mdS then
      if let .thmInfo _ := c then
        throwError "the export reaches the Section 4 result proof {n} in {md}"
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
    if let .thmInfo _ := c then
      thmCount := thmCount + 1
      let concl := c.type.getForallBody.getAppFn.constName?
      if concl == some ``HarmonicBalls.TypicalPointManyGoodScalesStmt then
        throwError "{n} proves the open Lemma 8.2 obligation: h82 must remain a binder of the derived route"
      if forbiddenConcl.any (fun s => concl == some s) then
        throwError "{n} proves a Section 4 statement or Lemma 8.2: the Sec9 route must not use it"
      if concl == some ``HarmonicBalls.LQGVolumeGrowthAllScalesStmt then
        i2Producers := i2Producers.push n
      let mut t := c.type
      while t.isForall do
        if t.bindingDomain!.getForallBody.getAppFn.constName? == some ``HarmonicBalls.LQGVolumeGrowthAllScalesStmt then
          i2Binders := i2Binders.push n
          break
        t := t.bindingBody!
    let mut kids : Array Name := c.type.getUsedConstants
    if let some v := valOf c then
      kids := kids ++ v.getUsedConstants
    for k in kids do
      unless parent.contains k do
        parent := parent.insert k n
        todo := todo.push k
  logInfo m!"closure: {hbCount} HarmonicBalls declarations ({thmCount} theorems) in {hbMods.size} modules; \
    Proposed/External Props reached: {propDefs.toList}; aux obligations: {auxNames.toList}; \
    LatticeProb modules: {latMods.size}"
  logInfo m!"HarmonicBalls modules reached: {hbMods.toList}"
  logInfo m!"Section 4 and Section 10 declarations reached (watched, not forbidden; declaration <- first parent): \
    {watched.toList}"
  logInfo m!"I2 producers reached: {i2Producers.toList}; reached theorems with an I2 binder: {i2Binders.toList}"
