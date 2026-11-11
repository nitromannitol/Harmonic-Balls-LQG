import HarmonicBalls.Proofs.Sec6.DerivedInputAssembly
import HarmonicBalls.Proofs.Sec9.WeakUniquenessDerivedInputs
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Propositions 6.1 and 6.2 from three staged measure inputs and the open Section 6 leaves

Pure assembly: this module adds no mathematics.
It is a conditional reduction, not a closure of Proposition 6.1 or 6.2. Source review of the staged inputs is pending.

Exports. Four theorems at the frozen conclusions `HarnackTypeEstimateStmt` (Proposition 6.1,
`HarmonicBalls/Draft/Section6.lean:206`) and `HarnackTypeComponentStmt` (Proposition 6.2, line 230):

* `harnackTypeEstimateStmt_of_three_inputs` and `harnackTypeComponentStmt_of_three_inputs`;
* `harnackTypeEstimateStmt_of_three_inputs_steps` and `harnackTypeComponentStmt_of_three_inputs_steps`, where the
  Lemma 6.13 premise is replaced by its two steps `GoodAnnulusOdometerDecayStep` and `ComponentOdometerDiscMaxStep`
  (`HarmonicBalls/Steps/Sec6/LowMass.lean:35,48`).

Premises, and nothing else. The three staged measure inputs, at every carrier `Ω : Type u`:

* `hDG : WholePlaneLQGBallMassBounds` (whole-plane ball-mass bounds);
* `hCC : LQGMeasureCoordChange` at insertion `0` (coordinate change);
* `hE : LQGMeasureExistence` at EVERY insertion `α : ℝ` (existence; the all-insertion form that the staged I2 export
  `lqgVolumeGrowthAllScalesStmt_of_staged_inputs` takes as its third premise, `HarmonicBalls/Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53`);

and the open Section 6 leaves, kept as explicit hypotheses:

* `hsub : VeryGoodAnnuliSubRangeStep` (very good annuli);
* `h68 : AnnulusMassBoundByOdometerStmt` (Lemma 6.8), `h610 : OdometerBoundByAnnulusMassStmt` (Lemma 6.10);
* `h613 : LowMassSmallOdometerStmt` (Lemma 6.13), or `hdec` and `hdisc` in the `_steps` exports.

Discharged inside the module, so they are binders of no export:

* the Weyl scaling premise `LQGMeasureWeylScaling` at insertion `0`: `Section6Derived.lqgMeasureWeylScaling_univ`
  (`HarmonicBalls/Proofs/Sec6/DerivedInputAssembly.lean`);
* the existence premise `LQGMeasureExistence` at insertion `0`: `hE` specialised to `α = 0`;
* the affine invariance `WholePlaneGFFAffineInvariance`: inside I2, via `wholePlaneGFFAffineInvariance_univ`;
* Lemma 3.2, `ClusterOpenLaplacianStmt`: `clusterOpenLaplacian_proved` (`HarmonicBalls/Proofs/Sec3/OpenLaplacian.lean:25`)
  applied to I2.

Comparison with the existing exports (no duplicate). `section6_of_literature_without_weyl`
(`HarmonicBalls/Proofs/Sec6/Section6FromLiterature.lean`) and `section6_of_volumeGrowth`
(`HarmonicBalls/Proofs/Sec6/Section6FromVolumeGrowth.lean`) take the affine premise and conclude all thirteen Section 6
statements. They obtain the four leaves from all-scales volume growth through the annulus iteration. The exports here take
neither the affine premise nor the non-atomicity premise `hN`, and they take the four leaves as hypotheses instead. The
guard below checks that their closure does not reach `HarmonicBalls.Section6.annulusIterationStmt_proved`.

Credit: Leonardo Bonanno. Two modules of his `LatticeProb` library, `LatticeProb.Prob.MaximalErgodic` and
`LatticeProb.Prob.Birkhoff`, lie in the import closure of this module, through
`HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean` (the provider of the Weyl premise), as recorded in
`HarmonicBalls/Proofs/Sec6/DerivedInputAssembly.lean`. The constant closure of the four exports reaches no LatticeProb
declaration (guard: no LatticeProb module reached). By contrast, `section6_of_volumeGrowth` applied to I2 reaches the annulus
iteration and about 194 LatticeProb modules, among them `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`, which holds his
proof of the Gwynne–Miller lemma (recorded in `docs/campaign/audits/Section6ThreeInputAssembly.md`). These
exports do not use that route.
-/

namespace HarmonicBalls

universe u

open MeasureTheory

namespace Section6ThreeInput

/-- **Proposition 6.1** (`HarnackTypeEstimateStmt`, `HarmonicBalls/Draft/Section6.lean:206`) from the three staged
measure inputs `hDG`, `hCC`, `hE` and the open leaves `hsub`, `h68`, `h610`, `h613`. The Weyl premise is
discharged by `Section6Derived.lqgMeasureWeylScaling_univ`, the existence premise at insertion `0` is `hE` at `α = 0`,
and the Lemma 3.2 premise `ClusterOpenLaplacianStmt` is `clusterOpenLaplacian_proved` applied to I2. -/
theorem harnackTypeEstimateStmt_of_three_inputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u}) (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (h613 : LowMassSmallOdometerStmt.{u}) :
    HarnackTypeEstimateStmt.{u} :=
  Section6Derived.harnackTypeEstimateStmt_of_derived_weyl hsub
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
    (clusterOpenLaplacian_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE))
    h68 h610 h613

/-- **Proposition 6.2** (`HarnackTypeComponentStmt`, `HarmonicBalls/Draft/Section6.lean:230`) from the three staged
measure inputs `hDG`, `hCC`, `hE` and the open leaves `hsub`, `h68`, `h610`, `h613`. The premises discharged inside
the module are those of `harnackTypeEstimateStmt_of_three_inputs`. -/
theorem harnackTypeComponentStmt_of_three_inputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u}) (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (h613 : LowMassSmallOdometerStmt.{u}) :
    HarnackTypeComponentStmt.{u} :=
  Section6Derived.harnackTypeComponentStmt_of_derived_weyl hsub
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
    (clusterOpenLaplacian_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE))
    h68 h610 h613

/-- **Proposition 6.1** with the Lemma 6.13 premise given by its two steps `hdec` (good-annulus odometer decay) and
`hdisc` (component odometer discrete maximum). Same premises as `harnackTypeEstimateStmt_of_three_inputs` otherwise. -/
theorem harnackTypeEstimateStmt_of_three_inputs_steps
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u}) (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (hdec : GoodAnnulusOdometerDecayStep.{u}) (hdisc : ComponentOdometerDiscMaxStep.{u}) :
    HarnackTypeEstimateStmt.{u} :=
  Section6Derived.harnackTypeEstimateStmt_of_derived_weyl_steps hsub
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
    (clusterOpenLaplacian_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE))
    h68 h610 hdec hdisc

/-- **Proposition 6.2** with the Lemma 6.13 premise given by its two steps `hdec` and `hdisc`. Same premises as
`harnackTypeComponentStmt_of_three_inputs` otherwise. -/
theorem harnackTypeComponentStmt_of_three_inputs_steps
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u}) (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (hdec : GoodAnnulusOdometerDecayStep.{u}) (hdisc : ComponentOdometerDiscMaxStep.{u}) :
    HarnackTypeComponentStmt.{u} :=
  Section6Derived.harnackTypeComponentStmt_of_derived_weyl_steps hsub
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
    (clusterOpenLaplacian_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE))
    h68 h610 hdec hdisc

end Section6ThreeInput


-- Guard: standard axioms only; each export takes exactly hDG, hCC, hE and its open leaves (no affine, Weyl or Lemma 3.2
-- binder); the hE binder quantifies over every insertion α and equals the premise of the staged I2 export; the closure
-- reaches no non-definitional Proposed or External constant and no theorem concluding Lemma 8.2.
open Lean Meta Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let exports : Array Name := #[``HarmonicBalls.Section6ThreeInput.harnackTypeEstimateStmt_of_three_inputs,
    ``HarmonicBalls.Section6ThreeInput.harnackTypeComponentStmt_of_three_inputs,
    ``HarmonicBalls.Section6ThreeInput.harnackTypeEstimateStmt_of_three_inputs_steps,
    ``HarmonicBalls.Section6ThreeInput.harnackTypeComponentStmt_of_three_inputs_steps]
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
  let base : Array String := #["HarmonicBalls.WholePlaneLQGBallMassBounds",
    "HarmonicBalls.LQGMeasureCoordChange", "HarmonicBalls.LQGMeasureExistence",
    "HarmonicBalls.VeryGoodAnnuliSubRangeStep", "HarmonicBalls.AnnulusMassBoundByOdometerStmt",
    "HarmonicBalls.OdometerBoundByAnnulusMassStmt"]
  let baseN : Array String := #["hDG", "hCC", "hE", "hsub", "h68", "h610"]
  let stepHeads : Array String := #["HarmonicBalls.GoodAnnulusOdometerDecayStep",
    "HarmonicBalls.ComponentOdometerDiscMaxStep"]
  let spec : Array (Array String × Array String × Name) := #[
    (baseN.push "h613", base.push "HarmonicBalls.LowMassSmallOdometerStmt", ``HarmonicBalls.HarnackTypeEstimateStmt),
    (baseN.push "h613", base.push "HarmonicBalls.LowMassSmallOdometerStmt", ``HarmonicBalls.HarnackTypeComponentStmt),
    (baseN ++ #["hdec", "hdisc"], base ++ stepHeads, ``HarmonicBalls.HarnackTypeEstimateStmt),
    (baseN ++ #["hdec", "hdisc"], base ++ stepHeads, ``HarmonicBalls.HarnackTypeComponentStmt)]
  for i in [0:exports.size] do
    let p := exports[i]!
    let (ns, hs, cl) := spec[i]!
    let some ci := env.find? p | throwError "export missing: {p}"
    let bs := binders ci.type
    unless bs.map (·.1) == ns do
      throwError "{p}: binders {bs.map (·.1)} differ from {ns}"
    unless bs.map (fun b => headOf b.2) == hs do
      throwError "{p}: premise heads {bs.map (fun b => headOf b.2)} differ from {hs}"
    for j in [0:3] do
      unless bs[j]!.2 == refB[j]!.2 do
        throwError "{p}: premise {bs[j]!.1} differs from the premise of lqgVolumeGrowthAllScalesStmt_of_staged_inputs"
    let hEb := binders bs[2]!.2
    unless hEb.size == 7 && hEb[4]!.1 == "α" do
      throwError "{p}: premise hE does not quantify over every insertion α"
    unless ci.type.getForallBody.getAppFn.constName? == some cl do
      throwError "{p}: conclusion differs from {cl}"
  -- Closure of the four exports.
  let valOf : ConstantInfo → Option Expr := fun c => match c with
    | .defnInfo v => some v.value
    | .thmInfo v => some v.value
    | _ => none
  let mut todo : Array Name := #[]
  let mut queued : NameSet := {}
  for p in exports do
    if let some c := env.find? p then
      for k in c.type.getUsedConstants ++ ((valOf c).map (·.getUsedConstants)).getD #[] do
        unless queued.contains k do
          queued := queued.insert k
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
      if c.type.getForallBody.getAppFn.constName? == some ``HarmonicBalls.TypicalPointManyGoodScalesStmt then
        throwError "{n} proves the open Lemma 8.2 obligation: the exports must not reach it"
    let mut kids : Array Name := c.type.getUsedConstants
    if let some v := valOf c then
      kids := kids ++ v.getUsedConstants
    for k in kids do
      unless queued.contains k do
        queued := queued.insert k
        todo := todo.push k
  logInfo m!"Section6ThreeInput: standard axioms only for the four exports; each export takes exactly hDG hCC hE and its open leaves; no affine, Weyl or Lemma 3.2 binder; hE quantifies over every insertion α and equals the premise of lqgVolumeGrowthAllScalesStmt_of_staged_inputs"
  logInfo m!"closure: {hbCount} HarmonicBalls declarations ({thmCount} theorems) in {hbMods.size} modules; Proposed/External Props reached: {propDefs.toList}; aux obligations: {auxNames.toList}"
  logInfo m!"LatticeProb modules reached: {latMods.toList}"
  logInfo m!"annulus iteration HarmonicBalls.Section6.annulusIterationStmt_proved reached: {seen.contains ``HarmonicBalls.Section6.annulusIterationStmt_proved}; Section 4 declarations reached: {sec4Count}; Section 10 declarations reached: {sec10Count}"

end HarmonicBalls
