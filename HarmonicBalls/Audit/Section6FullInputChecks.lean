import HarmonicBalls.Proofs.Sec6.FullThreeInputAssembly
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Audit: the full thirteen-result Section 6 conjunction from three staged inputs

Credit: Leonardo Bonanno (annulus iteration, `annulusIterationStmt_proved`, through the
`LatticeProb.Bonanno` modules). Source-review status of the staged Proposed inputs remains pending.
The guard below checks printed constants, the frozen conclusion order, the premise domains against the
staged I2 export and the volume-growth producer, consumption of each premise, and the closure reach with
the closure producers of every reached Prop head and of every frozen statement.
-/

#print axioms HarmonicBalls.Section6Full.section6Full_of_three_inputs
#print axioms HarmonicBalls.Section6Full.harnackTypeEstimateStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.harnackTypeComponentStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.manyGoodAnnuliStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.goodAnnulusProbabilityStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.annulusIterationStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.manyVeryGoodAnnuliStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.veryGoodAnnulusProbabilityStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.annulusMassBoundByOdometerStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.odometerHarmonicMeasureBoundStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.odometerBoundByAnnulusMassStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.veryGoodAnnulusHarnackTypeStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.shellDecompositionStmt_of_three_inputs
#print axioms HarmonicBalls.Section6Full.lowMassSmallOdometerStmt_of_three_inputs

open Lean Meta Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let main := ``HarmonicBalls.Section6Full.section6Full_of_three_inputs
  let typed : Array Name := #[
    ``HarmonicBalls.Section6Full.harnackTypeEstimateStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.harnackTypeComponentStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.manyGoodAnnuliStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.goodAnnulusProbabilityStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.annulusIterationStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.manyVeryGoodAnnuliStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.veryGoodAnnulusProbabilityStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.annulusMassBoundByOdometerStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.odometerHarmonicMeasureBoundStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.odometerBoundByAnnulusMassStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.veryGoodAnnulusHarnackTypeStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.shellDecompositionStmt_of_three_inputs,
    ``HarmonicBalls.Section6Full.lowMassSmallOdometerStmt_of_three_inputs]
  let stmts : Array Name := #[
    ``HarmonicBalls.HarnackTypeEstimateStmt, ``HarmonicBalls.HarnackTypeComponentStmt,
    ``HarmonicBalls.ManyGoodAnnuliStmt, ``HarmonicBalls.GoodAnnulusProbabilityStmt,
    ``HarmonicBalls.AnnulusIterationStmt, ``HarmonicBalls.ManyVeryGoodAnnuliStmt,
    ``HarmonicBalls.VeryGoodAnnulusProbabilityStmt, ``HarmonicBalls.AnnulusMassBoundByOdometerStmt,
    ``HarmonicBalls.OdometerHarmonicMeasureBoundStmt, ``HarmonicBalls.OdometerBoundByAnnulusMassStmt,
    ``HarmonicBalls.VeryGoodAnnulusHarnackTypeStmt, ``HarmonicBalls.ShellDecompositionStmt,
    ``HarmonicBalls.LowMassSmallOdometerStmt]
  let exports : Array Name := #[main] ++ typed
  -- Standard constants only, for the main export and the thirteen typed exports.
  for p in exports do
    for a in (← liftCoreM (collectAxioms p)) do
      unless std.contains a do
        throwError "{p} depends on the non-standard constant {a}"
  -- Leading foralls of a type as (binder name, binder domain).
  let binders : Expr → Array (String × Expr) := fun e => Id.run do
    let mut out : Array (String × Expr) := #[]
    let mut t := e
    while t.isForall do
      out := out.push (t.bindingName!.toString, t.bindingDomain!)
      t := t.bindingBody!
    return out
  -- Head constant of a binder domain, after its own foralls.
  let headOf : Expr → String := fun e =>
    ((e.getForallBody.getAppFn.constName?).map toString).getD "?"
  -- Right-nested conjuncts of a conclusion.
  let conjuncts : Expr → Array Expr := fun e => Id.run do
    let mut out : Array Expr := #[]
    let mut t := e
    while t.isAppOfArity ``And 2 do
      out := out.push t.appFn!.appArg!
      t := t.appArg!
    return out.push t
  -- A proof consumes the three premises when its body, after three leading lambdas, uses each of them.
  let consumes : Expr → Bool := fun v => Id.run do
    let mut b := v
    for _ in [0:3] do
      unless b.isLambda do return false
      b := b.bindingBody!
    return b.hasLooseBVar 0 && b.hasLooseBVar 1 && b.hasLooseBVar 2
  let valOf : ConstantInfo → Option Expr := fun c => match c with
    | .defnInfo v => some v.value
    | .thmInfo v => some v.value
    | _ => none
  let some mainC := env.find? main | throwError "the main export is missing"
  let some i2 := env.find? ``HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_staged_inputs
    | throwError "the staged I2 export is missing"
  let some s6 := env.find? ``HarmonicBalls.Section6.section6_of_volumeGrowth
    | throwError "the volume-growth producer is missing"
  let mainB := binders mainC.type
  let i2B := binders i2.type
  let s6B := binders s6.type
  unless mainB.map (·.1) == #["hDG", "hCC", "hE"] do
    throwError "the main export has binders {mainB.map (·.1)} instead of hDG hCC hE"
  for j in [0:3] do
    unless mainB[j]!.2 == i2B[j]!.2 do
      throwError "premise {mainB[j]!.1} differs from the premise of lqgVolumeGrowthAllScalesStmt_of_staged_inputs"
  unless mainB[1]!.2 == s6B[2]!.2 do
    throwError "hCC differs from the coordinate-change premise (insertion 0) of section6_of_volumeGrowth"
  unless (headOf mainB[0]!.2 == "HarmonicBalls.WholePlaneLQGBallMassBounds") && (headOf mainB[1]!.2 == "HarmonicBalls.LQGMeasureCoordChange") && (headOf mainB[2]!.2 == "HarmonicBalls.LQGMeasureExistence") do
    throwError "premise heads differ from the three staged Proposed inputs"
  let hEb := binders mainB[2]!.2
  unless hEb.size == 7 && hEb[4]!.1 == "α" do
    throwError "hE does not quantify over every insertion α"
  let some mv := valOf mainC | throwError "the main export has no value"
  unless consumes mv && mv.getUsedConstants.contains ``HarmonicBalls.Section6.section6_of_volumeGrowth do
    throwError "the main export does not consume hDG hCC hE through section6_of_volumeGrowth"
  let concl := (conjuncts mainC.type.getForallBody).map (fun c => c.getAppFn.constName?)
  unless concl == stmts.map some do
    throwError "the conjunct heads {concl} differ from the thirteen frozen statements"
  for i in [0:typed.size] do
    let p := typed[i]!
    let some ci := env.find? p | throwError "typed export missing: {p}"
    let bs := binders ci.type
    unless bs.map (·.1) == #["hDG", "hCC", "hE"] do
      throwError "{p}: binders {bs.map (·.1)} differ from hDG hCC hE"
    for j in [0:3] do
      unless bs[j]!.2 == mainB[j]!.2 do
        throwError "{p}: premise {bs[j]!.1} differs from the main export"
    unless ci.type.getForallBody.getAppFn.constName? == some stmts[i]! do
      throwError "{p}: the conclusion differs from {stmts[i]!}"
    let some v := valOf ci | throwError "{p} has no value"
    unless consumes v do
      throwError "{p} does not consume each of hDG hCC hE"
  -- Closure of the fourteen exports.
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
  let mut stepDefs : Array Name := #[]
  let mut auxNames : Array Name := #[]
  let mut latMods : NameSet := {}
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
    if mdS.startsWith "HarmonicBalls.Steps" then
      if let .defnInfo _ := c then
        stepDefs := stepDefs.push n
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
  -- Closure producers: theorems in the closure whose conclusion head is a reached Prop head or a frozen statement.
  let heads : Array Name := propDefs ++ stepDefs ++ stmts
  let mut headSet : NameSet := {}
  for h in heads do
    headSet := headSet.insert h
  let mut producers : Array (Name × Name) := #[]
  for n in seen.toList do
    if let some c := env.find? n then
      if let .thmInfo _ := c then
        if let some h := c.type.getForallBody.getAppFn.constName? then
          if headSet.contains h then
            producers := producers.push (h, n)
  for h in heads do
    let ps := (producers.filter (fun q => q.1 == h)).map (·.2)
    logInfo m!"Prop head or frozen statement {h}: closure producers {ps.toList}"
  logInfo m!"Section6Full: standard constants only for the main export and the thirteen typed exports; premises hDG hCC hE with the domains of the staged I2 export; hCC at insertion 0 is the section6_of_volumeGrowth premise; hE quantifies over every insertion; conjunct heads are the thirteen frozen statements in order; each premise is consumed"
  logInfo m!"closure: {hbCount} HarmonicBalls declarations ({thmCount} theorems) in {hbMods.size} modules; Proposed/External Props: {propDefs.toList}; Steps Props: {stepDefs.toList}; Proposed/External auxiliary obligations: {auxNames.toList}"
  logInfo m!"LatticeProb modules reached: {latMods.size}; L3_4M6 (Bonanno) modules: {latMods.toList.filter (fun m => m.toString.endsWith "L3_4M6")}"
  logInfo m!"annulus iteration HarmonicBalls.Section6.annulusIterationStmt_proved reached: {seen.contains ``HarmonicBalls.Section6.annulusIterationStmt_proved}; Lemma 8.2 obligation producers reached: none (the guard throws otherwise)"
