import HarmonicBalls.Proofs.Sec3.DerivedInputAssembly
import HarmonicBalls.Proofs.Sec4.ClusterLowerBound
import HarmonicBalls.Proofs.Sec4.LeastSupersolutionHolder
import HarmonicBalls.Proofs.Sec4.ClusterGreenIdentity
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Section 4 input consumption checks (Proposition 4.1, Lemmas 4.2-4.3)

Independent type checks of the three exports of `HarmonicBalls/Proofs/Sec4/` against the frozen statements of
`HarmonicBalls/Draft/Section4.lean`: `ClusterLowerBoundStmt` (Proposition 4.1, line 95), `LeastSupersolutionHolderStmt`
(Lemma 4.2, line 116) and `ClusterSubharmonicBallStmt` (Lemma 4.3, line 132).

* Literature route: `clusterLowerBound_of_literature`, `leastSupersolutionHolder_of_literature` and
  `clusterSubharmonicBall_of_literature`. Their only hypotheses are the six staged premises of
  `HarmonicBalls/Proposed/LQG.lean`, kept explicit in the universe `u`: `hDG` (`WholePlaneLQGBallMassBounds`), `hAff`
  (`WholePlaneGFFAffineInvariance`), `hCC` (`LQGMeasureCoordChange`), `hW` (`LQGMeasureWeylScaling`), `hE`
  (`LQGMeasureExistence`) and `hN` (`LQGMeasureNonatomic`). They are pending operator source-check; this file does not
  certify them.
* Input I2 (`LQGVolumeGrowthAllScalesStmt`, `HarmonicBalls/Draft/Section2.lean`) is not a hypothesis of the literature
  route. It is produced by `lqgVolumeGrowthAllScalesStmt_of_literature` (`HarmonicBalls/Proofs/Sec2/Assembly.lean`) from
  the same six premises; that producer's proof also uses the proved theorem `wholePlaneGFFMixtureStep_holds`.
* Proof route: `clusterLowerBound_proved`, `leastSupersolutionHolder_proved` and `clusterSubharmonicBall_proved` take I2
  as their only hypothesis and mention none of the six premises in their types.
* Kernel orientation: `greenPotential O μ z = ∫ y, greenFunction O z y ∂μ` (pole in the first argument, as in
  Armitage-Gardiner and Proposition 2.3) and the junk value `greenFunction O x x = 0` on the diagonal.
* Each check is a typed `example` applying an export to its hypotheses. No standing-assumption package is introduced,
  no frozen statement is edited, and no numbered result is closed by this file.
* Derived route: the affine and Weyl premises discharged by the carrier-universal providers
  `wholePlaneGFFAffineInvariance_univ` and `lqgMeasureWeylScaling_univ` (`HarmonicBalls/Proofs/Sec3/DerivedInputAssembly.lean`),
  so the exports take only the four retained premises `hDG`, `hCC`, `hE`, `hN`. The providers are checked by the guard below.
* Credit: this module imports, through the derived providers, the LatticeProb library of Leonardo Bonanno
  (`LatticeProb.Bonanno`, Lattice-Probability lean-v4.35 dependency). Its import closure contains the HarmonicBalls
  modules that credit him, among them `HarmonicBalls/Proofs/Sec3/DerivedInputAssembly.lean`,
  `HarmonicBalls/Proofs/Sec9/AffineInvarianceAssembly.lean` (affine provider), `HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean`
  (Weyl provider), `HarmonicBalls/Proofs/Sec6/AnnulusIteration.lean` (Bonanno's proof of the Gwynne-Miller annulus
  iteration lemma), the Section 8 Birkhoff and circle-density ports and `HarmonicBalls/Proposed/Birkhoff.lean`. The guard
  below counts the LatticeProb modules reached.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

section LiteratureRoutes

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

-- Input I2 through its Section 2 producer (Draft/Section2.lean:122).
example : LQGVolumeGrowthAllScalesStmt.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN

-- Proposition 4.1 (Draft/Section4.lean:95).
example : ClusterLowerBoundStmt.{u} :=
  clusterLowerBound_of_literature hDG hAff hCC hW hE hN

-- Lemma 4.2 (Draft/Section4.lean:116).
example : LeastSupersolutionHolderStmt.{u} :=
  leastSupersolutionHolder_of_literature hDG hAff hCC hW hE hN

-- Lemma 4.3 (Draft/Section4.lean:132).
example : ClusterSubharmonicBallStmt.{u} :=
  clusterSubharmonicBall_of_literature hDG hAff hCC hW hE hN

end LiteratureRoutes

section DerivedRoutes

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

-- The affine and Weyl premises are the providers (their binders are carrier, measure and field data only).
example : ClusterLowerBoundStmt.{u} :=
  clusterLowerBound_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

example : LeastSupersolutionHolderStmt.{u} :=
  leastSupersolutionHolder_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

example : ClusterSubharmonicBallStmt.{u} :=
  clusterSubharmonicBall_of_literature hDG wholePlaneGFFAffineInvariance_univ hCC lqgMeasureWeylScaling_univ hE hN

end DerivedRoutes

section ProofRoutes

-- The proof routes take I2 as their only hypothesis.
example (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : ClusterLowerBoundStmt.{u} :=
  clusterLowerBound_proved hI2

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : LeastSupersolutionHolderStmt.{u} :=
  leastSupersolutionHolder_proved hI2

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : ClusterSubharmonicBallStmt.{u} :=
  clusterSubharmonicBall_proved hI2

end ProofRoutes

section KernelOrientation

-- Orientation of `greenPotential` (Defs/Green.lean): the pole of `G_O` is the first argument.
example (O : Set ℂ) (μ : MeasureTheory.Measure ℂ) (z : ℂ) :
    greenPotential O μ z = ∫ y, greenFunction O z y ∂μ :=
  rfl

-- Junk value of `greenFunction` on the diagonal (Defs/Green.lean).
example (O : Set ℂ) (x : ℂ) : greenFunction O x x = 0 := by
  simp [greenFunction]

end KernelOrientation

#print axioms clusterLowerBound_of_literature
#print axioms leastSupersolutionHolder_of_literature
#print axioms clusterSubharmonicBall_of_literature
#print axioms lqgVolumeGrowthAllScalesStmt_of_literature
#print axioms clusterLowerBound_proved
#print axioms leastSupersolutionHolder_proved
#print axioms clusterSubharmonicBall_proved
#print axioms wholePlaneGFFAffineInvariance_univ
#print axioms lqgMeasureWeylScaling_univ

open Lean in
/-- Constants of `HarmonicBalls` reached from `roots` through types and values (declarations only). -/
def sec4Reach (roots : Array Name) : Lean.Elab.Command.CommandElabM NameSet := do
  let env ← getEnv
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some mi := env.getModuleIdxFor? n | continue
    unless (env.header.moduleNames[mi]!).getRoot == `HarmonicBalls do continue
    let some ci := env.find? n | continue
    todo := todo ++ ci.type.getUsedConstants
    match ci with
    | .thmInfo tv => todo := todo ++ tv.value.getUsedConstants
    | .defnInfo dv => todo := todo ++ dv.value.getUsedConstants
    | _ => pure ()
  return seen

open Lean Elab Command in
/-- Every Proposed or External constant reached is a definition (a Prop-valued statement) or a proof obligation that
Lean abstracts out of such a definition; a reached theorem, or a constant without a definitional body, is an error. -/
def sec4CheckStaged (r : NameSet) : CommandElabM Unit := do
  let env ← getEnv
  for n in r.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let md := (env.header.moduleNames[mi]!).toString
    unless md.startsWith "HarmonicBalls.Proposed" || md.startsWith "HarmonicBalls.External" do continue
    let some ci := env.find? n | continue
    let isDef : Bool := match ci with
      | .defnInfo _ => true
      | _ => false
    let isAux : Bool := n.isInternalDetail && (match env.find? n.getPrefix with
      | some (.defnInfo _) => true
      | _ => false)
    unless isDef || isAux do
      throwError "the reached literature constant {n} in {md} is neither a definition nor a proof obligation of one"

-- Guards (an error fails the check): standard axioms only; LatticeProb modules are counted (credit in the header); the literature routes
-- have the six premises and no I2 hypothesis and apply the I2 producer; the proof routes take I2 and no premise and
-- do not reach the literature I2 producer; the I2 producer reaches no Section 3 or Section 4 declaration.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let lat := (env.header.moduleNames.filter (fun m => m.getRoot == `LatticeProb)).size
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let premises : Array Name := #[``WholePlaneLQGBallMassBounds, ``WholePlaneGFFAffineInvariance,
    ``LQGMeasureCoordChange, ``LQGMeasureWeylScaling, ``LQGMeasureExistence, ``LQGMeasureNonatomic]
  let lits : Array Name := #[``clusterLowerBound_of_literature, ``leastSupersolutionHolder_of_literature,
    ``clusterSubharmonicBall_of_literature]
  let props : Array Name := #[``clusterLowerBound_proved, ``leastSupersolutionHolder_proved,
    ``clusterSubharmonicBall_proved]
  let i2 := ``lqgVolumeGrowthAllScalesStmt_of_literature
  let valOf : ConstantInfo → Option Expr := fun c => match c with
    | .thmInfo tv => some tv.value
    | .defnInfo dv => some dv.value
    | _ => none
  let modOf : Name → String := fun n => match env.getModuleIdxFor? n with
    | some mi => (env.header.moduleNames[mi]!).toString
    | none => ""
  let staged : NameSet → String := fun s =>
    String.intercalate ", " ((s.toList.filter fun n => (modOf n).startsWith "HarmonicBalls.Proposed" ||
      (modOf n).startsWith "HarmonicBalls.External").map toString)
  let forbidden : List String := ["HarmonicBalls.Proofs.Sec3", "HarmonicBalls.Steps.Sec3",
    "HarmonicBalls.Draft.Section3", "HarmonicBalls.Proofs.Sec4", "HarmonicBalls.Steps.Sec4",
    "HarmonicBalls.Draft.Section4"]
  let rI2 ← sec4Reach #[i2]
  sec4CheckStaged rI2
  for n in rI2.toList do
    if forbidden.any (fun f => (modOf n).startsWith f) then
      throwError "the I2 producer reaches {n} in {modOf n}: circular dependency"
  for e in lits do
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
    unless v.getUsedConstants.contains i2 do
      throwError "{e} does not apply {i2}"
    let r ← sec4Reach #[e]
    sec4CheckStaged r
    logInfo m!"{e}: staged predecessors [{staged r}]; {r.toList.length} HarmonicBalls declarations reached"
  for e in props do
    for a in (← liftCoreM (collectAxioms e)) do
      unless std.contains a do
        throwError "{e} depends on the non-standard axiom {a}"
    let some ci := env.find? e | throwError "missing {e}"
    let tys := ci.type.getUsedConstants
    unless tys.contains ``LQGVolumeGrowthAllScalesStmt do
      throwError "{e} does not take I2 as its hypothesis"
    for p in premises do
      if tys.contains p then
        throwError "{e} has the literature premise {p} in its type"
    let r ← sec4Reach #[e]
    sec4CheckStaged r
    if r.contains i2 then
      throwError "{e} reaches the literature I2 producer"
    logInfo m!"{e}: staged predecessors [{staged r}]; {r.toList.length} HarmonicBalls declarations reached"
  -- Derived route: the providers are carrier-universal and their closure reaches no Section 4 declaration.
  let providers : Array Name := #[``wholePlaneGFFAffineInvariance_univ, ``lqgMeasureWeylScaling_univ]
  for p in providers do
    for a in (← liftCoreM (collectAxioms p)) do
      unless std.contains a do
        throwError "{p} depends on the non-standard axiom {a}"
  let forbidden4 : List String := ["HarmonicBalls.Proofs.Sec4", "HarmonicBalls.Steps.Sec4", "HarmonicBalls.Draft.Section4"]
  let rP ← sec4Reach providers
  sec4CheckStaged rP
  for n in rP.toList do
    if forbidden4.any (fun f => (modOf n).startsWith f) then
      throwError "the derived providers reach {n} in {modOf n}: circular dependency"
  logInfo m!"derived route: staged predecessors [{staged rP}]; {rP.toList.length} HarmonicBalls declarations reached by the providers"
  logInfo m!"Section4InputChecks: standard axioms; {lat} LatticeProb modules in the import closure (credited in the header); I2 is not a premise of the literature or derived routes; six premises on the literature routes, four on the derived routes; I2 consumed through lqgVolumeGrowthAllScalesStmt_of_literature; the I2 producer reaches {rI2.toList.length} HarmonicBalls declarations, none in Section 3 or 4"

end HarmonicBalls
