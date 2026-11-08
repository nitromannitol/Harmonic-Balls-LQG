import HarmonicBalls.Steps.SecA.AppendixA
import HarmonicBalls.Proofs.SecA.Basic
import HarmonicBalls.Proofs.SecA.ObstacleLeastSuperharmonicMajorant
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Proofs.SecA.ObstacleMonotone
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec3.ConservationOfMass
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep2
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep3
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Steps.Sec3.ClusterCompatibility
import HarmonicBalls.Steps.Sec2.GreenFunctionBall
import Lean.Util.CollectAxioms

/-!
# Appendix A input consumption checks (Lemmas A.1-A.6)

Independent typed checks of the Appendix A exports against the frozen statements of `HarmonicBalls/Draft/SectionA.lean`:
`ObstacleLeastSuperharmonicMajorantStmt` (line 48), `ObstacleNonCoincidenceHarmonicStmt` (62),
`ObstacleMonotoneStmt` (73), `ObstacleOdometerZeroBoundaryStmt` (80), `ObstacleConservationOfMassStmt` (90) and
`ObstacleCompatibilityStmt` (105). Each check applies an existing producer at the exact type it proves; no new
mathematical claim is made here, and no frozen statement is edited.

* Statement-level producers: `obstacleLeastSuperharmonicMajorant_holds` and `obstacleNonCoincidenceHarmonic_holds`
  (`HarmonicBalls/Proofs/SecA/ObstacleNonCoincidenceHarmonic.lean`), `obstacleMonotone_holds`
  (`HarmonicBalls/Proofs/SecA/ObstacleMonotone.lean`), `obstacleOdometerZeroBoundary_of_general` applied to
  `obstacleOdometerZeroBoundaryGeneral_holds` (`HarmonicBalls/Proofs/Sec3/Basic.lean`), `obstacleConservationOfMass_holds`
  (`HarmonicBalls/Proofs/Sec3/ConservationOfMassLemma.lean`) and `obstacleCompatibility_holds`
  (`HarmonicBalls/Proofs/Sec3/ClusterCompatibility.lean`).
* Step route: `appendixA_of_steps` (`HarmonicBalls/Steps/SecA/AppendixA.lean`) applied to the step producers; the two
  steps of Lemma A.6 are `obstacleCompatibilityStep{1,2}_of_pole` applied to `obstacleCompatibilityPoleStep{1,2}_holds`.
* Sign conventions (Armitage-Gardiner normalization, Proposition 2.3): `G_O(x,·) ≥ 0` off `x` and `ΔG_O(x,·) = -δ_x`;
  `Δq_{B_R} = -μ`; `β_t = -t G_{B_R}(z,·) + q_{B_R}`; `v_t = ṽ_t - β_t`.
* Universes: none. The six statements and every checked declaration are monomorphic (the guard below checks this).
* Literature: the guard reports every `HarmonicBalls.Proposed` or `HarmonicBalls.External` constant reached from the
  checks, and the number of LatticeProb modules in the import closure (no LatticeProb code is consumed here).
* A compiled check of exports is not the closure of a numbered result.
-/

namespace HarmonicBalls

open MeasureTheory Metric

/-! ## Statement-level exports (frozen statements of `Draft/SectionA.lean`) -/

/-- Lemma A.1 export: `ObstacleLeastSuperharmonicMajorantStmt` (Draft/SectionA.lean:48). -/
theorem appendixA1_export_check : ObstacleLeastSuperharmonicMajorantStmt :=
  obstacleLeastSuperharmonicMajorant_holds

/-- Lemma A.2 export: `ObstacleNonCoincidenceHarmonicStmt` (Draft/SectionA.lean:62). -/
theorem appendixA2_export_check : ObstacleNonCoincidenceHarmonicStmt :=
  obstacleNonCoincidenceHarmonic_holds

/-- Lemma A.3 export: `ObstacleMonotoneStmt` (Draft/SectionA.lean:73). -/
theorem appendixA3_export_check : ObstacleMonotoneStmt :=
  obstacleMonotone_holds

/-- Lemma A.4 export: `ObstacleOdometerZeroBoundaryStmt` (Draft/SectionA.lean:80), from the general radius and pole. -/
theorem appendixA4_export_check : ObstacleOdometerZeroBoundaryStmt :=
  obstacleOdometerZeroBoundary_of_general obstacleOdometerZeroBoundaryGeneral_holds

/-- Lemma A.5 export: `ObstacleConservationOfMassStmt` (Draft/SectionA.lean:90). -/
theorem appendixA5_export_check : ObstacleConservationOfMassStmt :=
  obstacleConservationOfMass_holds

/-- Lemma A.6 export: `ObstacleCompatibilityStmt` (Draft/SectionA.lean:105), from the Section 3 producer. -/
theorem appendixA6_export_check : ObstacleCompatibilityStmt :=
  obstacleCompatibility_holds

/-! ## Step route: the appendix assembly at the existing producers -/

/-- The six statements from the step producers through `appendixA_of_steps`. Each of the eighteen premises is a
producer theorem applied at its exact type, so the conjunction carries no premise of its own. -/
theorem appendixA_steps_check :
    ObstacleLeastSuperharmonicMajorantStmt ∧ ObstacleNonCoincidenceHarmonicStmt ∧ ObstacleMonotoneStmt ∧
      ObstacleOdometerZeroBoundaryStmt ∧ ObstacleConservationOfMassStmt ∧ ObstacleCompatibilityStmt :=
  appendixA_of_steps greenFunctionBall superharmonicOfLaplacianLEStep_holds laplacianLEOfSuperharmonicStep_holds
    hasLaplacianOfLaplacianLEGEStep_holds greenPotentialBallContinuousStep_holds greenPotentialBallLaplacianStep_holds
    obstacleTendstoAtBotStep_holds obstacleLeastSuperharmonicMajorantStep1_holds
    obstacleLeastSuperharmonicMajorantStep2_holds obstacleLeastSuperharmonicMajorantStep3_holds
    obstacleLeastSuperharmonicMajorantStep4_holds obstacleNonCoincidenceHarmonicStep2_holds
    obstacleNonCoincidenceHarmonicStep3_holds obstacleMonotoneStep1_holds
    obstacleConservationOfMassStep1_holds obstacleConservationOfMassStep2_holds obstacleConservationOfMassStep3_holds
    (obstacleCompatibilityStep1_of_pole obstacleCompatibilityPoleStep1_holds)
    (obstacleCompatibilityStep2_of_pole obstacleCompatibilityPoleStep2_holds)

/-- Lemma A.6 through its two steps (`obstacleCompatibility_of_steps`), the pole-zero steps being producers. -/
theorem appendixA6_steps_check : ObstacleCompatibilityStmt :=
  obstacleCompatibility_of_steps (obstacleCompatibilityStep1_of_pole obstacleCompatibilityPoleStep1_holds)
    (obstacleCompatibilityStep2_of_pole obstacleCompatibilityPoleStep2_holds)

/-! ## Sign conventions -/

/-- Green function sign convention (Proposition 2.3, `GreenFunctionBallStmt`): `ΔG_{B_R}(x,·) = -δ_x` on `B_R`, since
`HasLaplacian w μpos μneg U` means `Δw = μpos - μneg`, and `G_{B_R}(x,y) > 0` for `y ≠ x` in `B_R`. -/
theorem greenFunction_sign_check {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) :
    HasLaplacian (greenFunction (ball 0 R) x) 0 (Measure.dirac x) (ball 0 R) ∧
      ∀ y ∈ ball (0 : ℂ) R, y ≠ x → 0 < greenFunction (ball 0 R) x y :=
  ⟨(greenFunctionBall R hR x hx).1, fun y hy hyx => (greenFunctionBall R hR x hx).2.1 y hy hyx⟩

/-- Potential sign convention (eq:expected-exit-time): `Δq_{B_R} = -μ` on `B_R`, so the obstacle has
`Δβ_t = tδ_z - μ`. -/
theorem greenPotential_sign_check (μ : Measure ℂ) (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βm βp) :
    HasLaplacian (greenPotentialBall μ R) 0 μ (ball 0 R) :=
  greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV

/-- The obstacle is `β_t = -t G_{B_R}(z,·) + q_{B_R}` (eq:obstacle), by definition. -/
theorem obstacle_sign_check (μ : Measure ℂ) (R : ℝ) (z : ℂ) (t : ℝ) (x : ℂ) :
    obstacle μ R z t x = -t * greenFunction (ball 0 R) z x + greenPotentialBall μ R x :=
  rfl

/-- The shifted odometer is `v_t = ṽ_t - β_t` (eq:appendix-limit-odometer), by definition. -/
theorem shiftedOdometer_sign_check (μ : Measure ℂ) (R : ℝ) (z : ℂ) (t : ℝ) (x : ℂ) :
    shiftedOdometer μ R z t x = shiftedLeastSupersolution μ R z t x - obstacle μ R z t x :=
  rfl

/-! ## Axioms of the producers -/

#print axioms appendixA1_export_check
#print axioms appendixA2_export_check
#print axioms appendixA3_export_check
#print axioms appendixA4_export_check
#print axioms appendixA5_export_check
#print axioms appendixA6_export_check
#print axioms appendixA_steps_check
#print axioms appendixA6_steps_check
#print axioms greenFunctionBall
#print axioms greenPotentialBallLaplacianStep_holds
#print axioms obstacleConservationOfMassStep3_holds
#print axioms obstacleCompatibilityPoleStep1_holds

end HarmonicBalls

open Lean Elab Command in
/-- Constants of `HarmonicBalls` reached from `roots` through types and values (declarations only). -/
def appendixReach (roots : Array Name) : Lean.Elab.Command.CommandElabM NameSet := do
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
#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  -- each export check must have exactly the frozen statement as its type (no premises, no unfolded binders)
  let stmts : Array (Name × Name) := #[
    (`HarmonicBalls.appendixA1_export_check, `HarmonicBalls.ObstacleLeastSuperharmonicMajorantStmt),
    (`HarmonicBalls.appendixA2_export_check, `HarmonicBalls.ObstacleNonCoincidenceHarmonicStmt),
    (`HarmonicBalls.appendixA3_export_check, `HarmonicBalls.ObstacleMonotoneStmt),
    (`HarmonicBalls.appendixA4_export_check, `HarmonicBalls.ObstacleOdometerZeroBoundaryStmt),
    (`HarmonicBalls.appendixA5_export_check, `HarmonicBalls.ObstacleConservationOfMassStmt),
    (`HarmonicBalls.appendixA6_export_check, `HarmonicBalls.ObstacleCompatibilityStmt),
    (`HarmonicBalls.appendixA6_steps_check, `HarmonicBalls.ObstacleCompatibilityStmt)]
  let others : Array Name := #[
    `HarmonicBalls.appendixA_steps_check, `HarmonicBalls.greenFunction_sign_check,
    `HarmonicBalls.greenPotential_sign_check, `HarmonicBalls.obstacle_sign_check,
    `HarmonicBalls.shiftedOdometer_sign_check, `HarmonicBalls.greenFunctionBall,
    `HarmonicBalls.superharmonicOfLaplacianLEStep_holds, `HarmonicBalls.laplacianLEOfSuperharmonicStep_holds,
    `HarmonicBalls.hasLaplacianOfLaplacianLEGEStep_holds, `HarmonicBalls.greenPotentialBallContinuousStep_holds,
    `HarmonicBalls.greenPotentialBallLaplacianStep_holds, `HarmonicBalls.obstacleTendstoAtBotStep_holds,
    `HarmonicBalls.obstacleLeastSuperharmonicMajorantStep1_holds,
    `HarmonicBalls.obstacleLeastSuperharmonicMajorantStep2_holds,
    `HarmonicBalls.obstacleLeastSuperharmonicMajorantStep3_holds,
    `HarmonicBalls.obstacleLeastSuperharmonicMajorantStep4_holds,
    `HarmonicBalls.obstacleNonCoincidenceHarmonicStep2_holds, `HarmonicBalls.obstacleNonCoincidenceHarmonicStep3_holds,
    `HarmonicBalls.obstacleMonotoneStep1_holds, `HarmonicBalls.obstacleConservationOfMassStep1_holds,
    `HarmonicBalls.obstacleConservationOfMassStep2_holds, `HarmonicBalls.obstacleConservationOfMassStep3_holds,
    `HarmonicBalls.obstacleOdometerZeroBoundaryGeneral_holds, `HarmonicBalls.obstacleCompatibilityPoleStep1_holds,
    `HarmonicBalls.obstacleCompatibilityPoleStep2_holds, `HarmonicBalls.obstacleCompatibilityStep1_of_pole,
    `HarmonicBalls.obstacleCompatibilityStep2_of_pole]
  for (n, s) in stmts do
    let some ci := env.find? n | throwError "missing {n}"
    unless ci.type.constName? == some s do throwError "{n} does not have the frozen type {s}"
  let all : Array Name := stmts.map (·.1) ++ others
  for n in all do
    let some ci := env.find? n | throwError "missing {n}"
    unless ci.levelParams.isEmpty do throwError "{n} carries universe parameters"
    for a in (← liftCoreM (collectAxioms n)) do
      unless std.contains a do throwError "{n} depends on the non-standard axiom {a}"
  let r ← appendixReach all
  let mut lit : List Name := []
  for n in r.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let md := (env.header.moduleNames[mi]!).toString
    if md.startsWith "HarmonicBalls.Proposed" || md.startsWith "HarmonicBalls.External" then
      lit := n :: lit
  let lat := (env.header.moduleNames.filter (fun m => m.getRoot == `LatticeProb)).size
  logInfo m!"Appendix A checks: {all.size} declarations, standard axioms only, no universe parameters, no premises in the export types"
  logInfo m!"HarmonicBalls declarations reached: {r.toList.length}; literature constants reached (Proposed or External): {lit.length} {lit}"
  logInfo m!"LatticeProb modules in the import closure: {lat} (no LatticeProb code is consumed by this file)"
