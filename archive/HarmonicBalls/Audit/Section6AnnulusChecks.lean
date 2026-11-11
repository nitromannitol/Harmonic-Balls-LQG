import HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer
import HarmonicBalls.Proofs.Sec6.ShellDecomposition
import HarmonicBalls.Proofs.Sec6.Section6LiteratureAssembly
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Section 6 export checks: Lemma 6.5 (annulus iteration) and Lemma 6.12 (shell decomposition)

Lean-only audit. It adds no mathematics and makes no
numbered closure. It restates two proved declarations at their exact frozen types and checks, by constant
closure, which declarations they reach.

* **Lemma 6.5** (`lemma:annulus-iterate`, corrected tex line 1266; preserved arXiv source line 1262; cited there as
  `gwynne2020local`, Lemma 3.1). Frozen statement `HarmonicBalls.AnnulusIterationStmt`
  (`HarmonicBalls/Draft/Section6.lean:289`). Provider `HarmonicBalls.Section6.annulusIterationStmt_proved`
  (`HarmonicBalls/Proofs/Sec6/AnnulusLawTransfer.lean:207`). Its proof applies
  `HarmonicBalls.Section6.annulus_iteration_range_of_distribution` (`HarmonicBalls/Proofs/Sec6/AnnulusIteration.lean:66`),
  which applies Leonardo Bonanno's formalization `LQGMetric.LM.lmLem3_1a` (module
  `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`; his source `LM` is Gwynne–Miller, *Local metrics of the
  Gaussian free field*, arXiv:1905.00379). The law transfer from his whole-plane field setting to the frozen
  pairing-valued GFF uses `LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`, `.CircleAvgRate` and `.ExistGFF`;
  Leonardo Bonanno is credited for this bridge in `AnnulusLawTransfer.lean`.
* **Lemma 6.12** (`lemma:shell-decomposition`, corrected tex line 1640; preserved arXiv source line 1636).
  Frozen statement `HarmonicBalls.ShellDecompositionStmt` (`HarmonicBalls/Draft/Section6.lean:442`). Provider
  `HarmonicBalls.shellDecompositionStmt_proved` (`HarmonicBalls/Proofs/Sec6/ShellDecomposition.lean:164`).
  No literature input and no Bonanno module.

A compiled implication is not a source admission: the printed paper still cites Lemma 6.5 without a proof.

-/

namespace HarmonicBalls

universe u

open Lean

-- Lemma 6.5 at its exact frozen type (Bonanno's LM Lemma 3.1 with N = 0, through the law-transfer bridge).
example : AnnulusIterationStmt.{u} := Section6.annulusIterationStmt_proved

-- Lemma 6.12 at its exact frozen type (no literature input).
example : ShellDecompositionStmt := shellDecompositionStmt_proved

/-- Walks the constants reached from `todo` through `HarmonicBalls` declarations (types and values). It returns the
`HarmonicBalls` constants visited and the `LatticeProb` constants reached directly, with their modules;
`LatticeProb` declarations are not traversed. -/
partial def hbWalk (env : Environment) (todo : Array Name) (seen : NameSet) (hb : Array Name)
    (bnd : Array (Name × Name)) : Array Name × Array (Name × Name) :=
  match todo.back? with
  | none => (hb, bnd)
  | some n =>
    let todo := todo.pop
    if seen.contains n then hbWalk env todo seen hb bnd
    else
      let seen := seen.insert n
      match env.getModuleIdxFor? n with
      | none => hbWalk env todo seen hb bnd
      | some mi =>
        let md := env.header.moduleNames[mi]!
        if md.getRoot == `LatticeProb then hbWalk env todo seen hb (bnd.push (n, md))
        else if md.getRoot != `HarmonicBalls then hbWalk env todo seen hb bnd
        else
          match env.find? n with
          | none => hbWalk env todo seen (hb.push n) bnd
          | some ci =>
            let vals : Array Name := match ci with
              | .thmInfo tv => tv.value.getUsedConstants
              | .defnInfo dv => dv.value.getUsedConstants
              | _ => #[]
            hbWalk env ((todo ++ ci.type.getUsedConstants) ++ vals) seen (hb.push n) bnd

/-- True when the constant lives in the staged literature module `HarmonicBalls.Proposed`. -/
def isProposedConst (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some mi => (env.header.moduleNames[mi]!).toString.startsWith "HarmonicBalls.Proposed"
  | none => false

-- Guards (an error fails the check): standard axioms only for the two exports and for the Section 6 literature
-- assembly; each export has exactly its frozen Prop as type (no premises); the assembly takes neither Lemma 6.5 nor
-- Lemma 6.12 as a hypothesis; no `HarmonicBalls.Proposed` declaration is reached from either export; the Lemma 6.5
-- closure reaches `LQGMetric.LM.lmLem3_1a`; the Lemma 6.12 closure does not.
open Lean Elab Command in
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let ann : Name := ``Section6.annulusIterationStmt_proved
  let shl : Name := ``shellDecompositionStmt_proved
  let asm : Name := ``Section6.section6_of_greenPotential_and_literature
  let gm : Name := ``LQGMetric.LM.lmLem3_1a
  for e in #[ann, shl, asm] do
    for a in (← liftCoreM (collectAxioms e)) do
      unless std.contains a do
        throwError "{e} depends on {a}, which is outside propext, Classical.choice, Quot.sound"
  for (e, stmt) in #[(ann, ``AnnulusIterationStmt), (shl, ``ShellDecompositionStmt)] do
    let some ci := env.find? e | throwError "missing {e}"
    match ci.type with
    | .const n _ => unless n == stmt do throwError "{e} has type {n}, not {stmt}"
    | _ => throwError "{e} has a type with premises, not the bare frozen Prop"
  let some cA := env.find? asm | throwError "missing {asm}"
  let mut t := cA.type
  while t.isForall do
    for s in #[``AnnulusIterationStmt, ``ShellDecompositionStmt] do
      if t.bindingDomain!.getUsedConstants.contains s then
        throwError "{asm} takes {s} as a hypothesis"
    t := t.bindingBody!
  -- Positive control: the detector sees the staged literature premises that the assembly takes as hypotheses.
  unless (hbWalk env cA.type.getUsedConstants {} #[] #[]).1.any (isProposedConst env) do
    throwError "the Proposed detector is inert: the assembly type should reach its staged premises"
  let (hbA, bndA) := hbWalk env #[ann] {} #[] #[]
  let (hbS, bndS) := hbWalk env #[shl] {} #[] #[]
  if hbA.any (isProposedConst env) || hbS.any (isProposedConst env) then
    throwError "a HarmonicBalls.Proposed declaration is reached from Lemma 6.5 or Lemma 6.12"
  unless bndA.any (fun p => p.1 == gm) do
    throwError "the Lemma 6.5 closure does not reach {gm}"
  if bndS.any (fun p => p.1 == gm) then
    throwError "the Lemma 6.12 closure reaches {gm}"
  let mods (b : Array (Name × Name)) : String :=
    String.intercalate ", " ((b.map (fun p => p.2.toString)).toList.eraseDups)
  logInfo m!"Section6AnnulusChecks: standard axioms; exact frozen types; no Lemma 6.5 or 6.12 hypothesis in {asm}; no HarmonicBalls.Proposed declaration reached. Lemma 6.5 closure: {hbA.size} HarmonicBalls constants, LatticeProb modules [{mods bndA}]. Lemma 6.12 closure: {hbS.size} HarmonicBalls constants, LatticeProb modules [{mods bndS}]."

end HarmonicBalls
