import HarmonicBalls.Proofs.Sec6.Assembly
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling
import HarmonicBalls.Proofs.Sec6.ShellDecomposition
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Propositions 6.1 and 6.2 with the Weyl-scaling premise discharged

`HarmonicBalls/Proofs/Sec6/Assembly.lean` reduces Proposition 6.1 (`HarnackTypeEstimateStmt`,
`HarmonicBalls/Draft/Section6.lean:206`) and Proposition 6.2 (`HarnackTypeComponentStmt`, line 230) to a list of premises.
Its premise `hW` is `LQGMeasureWeylScaling P γ 0 hC hcirc` at every carrier `Ω : Type u`. This file discharges `hW`
internally: `lqgMeasureWeylScaling_univ` is `HarmonicBalls.Section6.lqgMeasureWeylScaling`
(`HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean`), which takes no further premise.

The exports keep every other premise as an explicit hypothesis, at its existing exact Prop:

* `hsub : VeryGoodAnnuliSubRangeStep` (very good annuli; `HarmonicBalls/Steps/Sec6/Prevalence.lean:54`);
* `hex : LQGMeasureExistence P γ 0` (staged in `HarmonicBalls/Proposed/LQG.lean`, pending operator source-check);
* `h32 : ClusterOpenLaplacianStmt` (Lemma 3.2; `HarmonicBalls/Draft/Section3.lean:66`);
* `h68 : AnnulusMassBoundByOdometerStmt` (Lemma 6.8) and `h610 : OdometerBoundByAnnulusMassStmt` (Lemma 6.10);
* `h613 : LowMassSmallOdometerStmt` (Lemma 6.13), or in the `_steps` variants its two steps
  `GoodAnnulusOdometerDecayStep` and `ComponentOdometerDiscMaxStep` (`HarmonicBalls/Steps/Sec6/LowMass.lean:35,48`).

The affine premise `WholePlaneGFFAffineInvariance` does not occur in these reductions, so no provider of it is used.
Lemma 6.12 (`ShellDecompositionStmt`, `HarmonicBalls/Draft/Section6.lean:442`) is exported at its frozen statement
from `shellDecompositionStmt_proved`.

These are conditional reductions. They are not a closure of Propositions 6.1 or 6.2: the leaves `hsub`, `hex`, `h32`,
`h68`, `h610` and `h613` remain open.

Credit: two modules of Leonardo Bonanno's `LatticeProb` library, `LatticeProb.Prob.MaximalErgodic` and
`LatticeProb.Prob.Birkhoff`, lie in the import closure of this module, through
`HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean` (the provider of the Weyl premise). The constant closure of the exports
reaches none of the declarations of that library (guard below), so these reductions use none of his results. The annulus
iteration of Lemma 6.5 uses his proof of the Gwynne–Miller lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`
(recorded in `HarmonicBalls/Proofs/Sec6/Section6FromVolumeGrowth.lean`); that proof is not used here.
-/

namespace HarmonicBalls

universe u

namespace Section6Derived

/-- Weyl scaling of the LQG measures at every carrier `Ω : Type u` with `α₀ = 0`, from
`HarmonicBalls.Section6.lqgMeasureWeylScaling` (`HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean`). It is the premise `hW`
of `harnackTypeComponentStmt_of_inputs` and `harnackTypeEstimateStmt_of_inputs`. -/
theorem lqgMeasureWeylScaling_univ :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc :=
  fun Ω _ P γ hC hcirc => HarmonicBalls.Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc

/-- **Proposition 6.2** (`HarnackTypeComponentStmt`, `HarmonicBalls/Draft/Section6.lean:230`) from the leaves `hsub`,
`hex`, `h32`, `h68`, `h610` and `h613`; its Weyl-scaling premise is `lqgMeasureWeylScaling_univ`. -/
theorem harnackTypeComponentStmt_of_derived_weyl (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (h32 : ClusterOpenLaplacianStmt.{u}) (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u}) (h613 : LowMassSmallOdometerStmt.{u}) :
    HarnackTypeComponentStmt.{u} :=
  harnackTypeComponentStmt_of_inputs hsub hex lqgMeasureWeylScaling_univ h32 h68 h610 h613

/-- **Proposition 6.1** (`HarnackTypeEstimateStmt`, `HarmonicBalls/Draft/Section6.lean:206`) from the same leaves;
its Weyl-scaling premise is `lqgMeasureWeylScaling_univ`. -/
theorem harnackTypeEstimateStmt_of_derived_weyl (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (h32 : ClusterOpenLaplacianStmt.{u}) (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u}) (h613 : LowMassSmallOdometerStmt.{u}) :
    HarnackTypeEstimateStmt.{u} :=
  harnackTypeEstimateStmt_of_inputs hsub hex lqgMeasureWeylScaling_univ h32 h68 h610 h613

/-- **Proposition 6.2** with Lemma 6.13 from its two steps `GoodAnnulusOdometerDecayStep` and
`ComponentOdometerDiscMaxStep` (`lowMassSmallOdometerStmt_of_steps`). -/
theorem harnackTypeComponentStmt_of_derived_weyl_steps (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (h32 : ClusterOpenLaplacianStmt.{u}) (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u}) (hdec : GoodAnnulusOdometerDecayStep.{u})
    (hdisc : ComponentOdometerDiscMaxStep.{u}) : HarnackTypeComponentStmt.{u} :=
  harnackTypeComponentStmt_of_inputs hsub hex lqgMeasureWeylScaling_univ h32 h68 h610
    (lowMassSmallOdometerStmt_of_steps hdec hdisc)

/-- **Proposition 6.1** with Lemma 6.13 from its two steps `GoodAnnulusOdometerDecayStep` and
`ComponentOdometerDiscMaxStep`. -/
theorem harnackTypeEstimateStmt_of_derived_weyl_steps (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (h32 : ClusterOpenLaplacianStmt.{u}) (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u}) (hdec : GoodAnnulusOdometerDecayStep.{u})
    (hdisc : ComponentOdometerDiscMaxStep.{u}) : HarnackTypeEstimateStmt.{u} :=
  harnackTypeEstimateStmt_of_inputs hsub hex lqgMeasureWeylScaling_univ h32 h68 h610
    (lowMassSmallOdometerStmt_of_steps hdec hdisc)

/-- **Lemma 6.12** (`ShellDecompositionStmt`, `HarmonicBalls/Draft/Section6.lean:442`) at its frozen statement, from
`shellDecompositionStmt_proved` (`HarmonicBalls/Proofs/Sec6/ShellDecomposition.lean`). -/
theorem shellDecompositionStmt_of_proved : ShellDecompositionStmt :=
  shellDecompositionStmt_proved

end Section6Derived

end HarmonicBalls

/-! ## Guards

The printed binders and axioms are the audit record. The meta guard below fails closed: the four Proposition exports
must conclude the frozen Props, keep their leaves as hypotheses and take no `LQGMeasureWeylScaling` hypothesis; every
export and provider must depend only on `propext`, `Classical.choice` and `Quot.sound`. -/

#check @HarmonicBalls.Section6Derived.harnackTypeEstimateStmt_of_derived_weyl
#check @HarmonicBalls.Section6Derived.harnackTypeComponentStmt_of_derived_weyl
#check @HarmonicBalls.Section6Derived.harnackTypeEstimateStmt_of_derived_weyl_steps
#check @HarmonicBalls.Section6Derived.harnackTypeComponentStmt_of_derived_weyl_steps
#check @HarmonicBalls.Section6Derived.shellDecompositionStmt_of_proved
#check @HarmonicBalls.Section6Derived.lqgMeasureWeylScaling_univ
#print axioms HarmonicBalls.Section6Derived.harnackTypeEstimateStmt_of_derived_weyl
#print axioms HarmonicBalls.Section6Derived.harnackTypeComponentStmt_of_derived_weyl
#print axioms HarmonicBalls.Section6Derived.harnackTypeEstimateStmt_of_derived_weyl_steps
#print axioms HarmonicBalls.Section6Derived.harnackTypeComponentStmt_of_derived_weyl_steps
#print axioms HarmonicBalls.Section6Derived.shellDecompositionStmt_of_proved
#print axioms HarmonicBalls.Section6Derived.lqgMeasureWeylScaling_univ

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let valOf : ConstantInfo → Option Expr := fun c => match c with
    | .thmInfo tv => some tv.value
    | .defnInfo dv => some dv.value
    | _ => none
  let leavesCommon : Array Name := #[``HarmonicBalls.VeryGoodAnnuliSubRangeStep,
    ``HarmonicBalls.LQGMeasureExistence, ``HarmonicBalls.ClusterOpenLaplacianStmt,
    ``HarmonicBalls.AnnulusMassBoundByOdometerStmt, ``HarmonicBalls.OdometerBoundByAnnulusMassStmt]
  let exps : Array (Name × Name × Array Name) := #[
    (``HarmonicBalls.Section6Derived.harnackTypeEstimateStmt_of_derived_weyl,
      ``HarmonicBalls.HarnackTypeEstimateStmt, leavesCommon ++ #[``HarmonicBalls.LowMassSmallOdometerStmt]),
    (``HarmonicBalls.Section6Derived.harnackTypeComponentStmt_of_derived_weyl,
      ``HarmonicBalls.HarnackTypeComponentStmt, leavesCommon ++ #[``HarmonicBalls.LowMassSmallOdometerStmt]),
    (``HarmonicBalls.Section6Derived.harnackTypeEstimateStmt_of_derived_weyl_steps,
      ``HarmonicBalls.HarnackTypeEstimateStmt,
      leavesCommon ++ #[``HarmonicBalls.GoodAnnulusOdometerDecayStep, ``HarmonicBalls.ComponentOdometerDiscMaxStep]),
    (``HarmonicBalls.Section6Derived.harnackTypeComponentStmt_of_derived_weyl_steps,
      ``HarmonicBalls.HarnackTypeComponentStmt,
      leavesCommon ++ #[``HarmonicBalls.GoodAnnulusOdometerDecayStep, ``HarmonicBalls.ComponentOdometerDiscMaxStep])]
  let shell : Name := ``HarmonicBalls.Section6Derived.shellDecompositionStmt_of_proved
  let weylUniv : Name := ``HarmonicBalls.Section6Derived.lqgMeasureWeylScaling_univ
  let all : Array Name := exps.map (·.1) ++ #[shell, weylUniv]
  for e in all do
    for a in (← liftCoreM (collectAxioms e)) do
      unless std.contains a do
        throwError "{e} depends on the non-standard constant {a}"
  for (e, p, leaves) in exps do
    let some ci := env.find? e | throwError "missing {e}"
    let tys := ci.type.getUsedConstants
    unless tys.contains p do
      throwError "{e} does not conclude the frozen statement {p}"
    if tys.contains ``HarmonicBalls.LQGMeasureWeylScaling then
      throwError "{e} still takes the Weyl premise as a hypothesis"
    for l in leaves do
      unless tys.contains l do
        throwError "{e} lacks the retained leaf {l}"
  let some sci := env.find? shell | throwError "missing {shell}"
  unless sci.type.getUsedConstants.contains ``HarmonicBalls.ShellDecompositionStmt do
    throwError "{shell} does not have the frozen statement ShellDecompositionStmt"
  let some wci := env.find? weylUniv | throwError "missing {weylUniv}"
  let some wv := valOf wci | throwError "{weylUniv} has no value"
  unless wv.getUsedConstants.contains ``HarmonicBalls.Section6.lqgMeasureWeylScaling do
    throwError "{weylUniv} does not apply HarmonicBalls.Section6.lqgMeasureWeylScaling"
  -- closure walk from the dependencies of the exports: HarmonicBalls, LatticeProb and this module's own constants
  -- are traversed; other imported roots (Mathlib, the Markov and elliptic packages) are not
  let mut todo : Array Name := #[]
  for e in all do
    let some ci := env.find? e | throwError "missing {e}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := valOf ci then
      todo := todo ++ v.getUsedConstants
  let mut seen : NameSet := {}
  let mut latMods : NameSet := {}
  let mut latConsts : NameSet := {}
  let mut propMods : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    match env.getModuleIdxFor? n with
    | some mi =>
      let md := env.header.moduleNames[mi]!
      unless md.getRoot == `HarmonicBalls || md.getRoot == `LatticeProb do continue
      if md.getRoot == `LatticeProb then
        latMods := latMods.insert md
        latConsts := latConsts.insert n
      if md.toString.startsWith "HarmonicBalls.Proposed" then propMods := propMods.insert md
    | none => pure ()
    todo := todo ++ ci.type.getUsedConstants
    if let some v := valOf ci then
      todo := todo ++ v.getUsedConstants
  let libMods := env.header.moduleNames.filter (fun m => m.getRoot == `LatticeProb)
  let latStr := ", ".intercalate (latMods.toList.map toString)
  let propStr := ", ".intercalate (propMods.toList.map toString)
  logInfo m!"Section6DerivedInputAssembly: LatticeProb modules in the import closure: {libMods.size}"
  logInfo m!"Section6DerivedInputAssembly: LatticeProb declarations reached by the exports: {latConsts.toList.length}"
  logInfo m!"Section6DerivedInputAssembly: LatticeProb modules reached: {latMods.toList.length} ({latStr})"
  logInfo m!"Section6DerivedInputAssembly: staged Proposed modules reached: {propMods.toList.length} ({propStr})"
  logInfo m!"Section6DerivedInputAssembly: guards passed for {all.size} declarations"
