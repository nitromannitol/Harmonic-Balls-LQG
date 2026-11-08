# Appendix A input consumption checks (Lemmas A.1-A.6)

Owner: worker z6. Lean file: `HarmonicBalls/Audit/AppendixInputChecks.lean` (new).
Frozen statements: `HarmonicBalls/Draft/SectionA.lean` (FROZEN.md rows 33-38). Read-only: Defs, Draft, FROZEN, External,
the preserved paper.

Verification (compile, not closure): `lc` OK (log `logs/lc/030905-2011204.log`); `lb HarmonicBalls.Audit.AppendixInputChecks`
BUILD OK (log `logs/lb/030954-2013735.log`). The guard in the file prints the figures quoted below.

## Result

* Each export check is a theorem whose declared type is exactly the frozen constant (checked by the guard through
  `ConstantInfo.type.constName?`). No check has an explicit premise.
* Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`) for the 34 checked declarations, and for the
  producers printed with `#print axioms`.
* No universe parameters on the 34 checked declarations.
* Reach from the checks: 2858 `HarmonicBalls` declarations (types and proof values). Constants of
  `HarmonicBalls.Proposed` or `HarmonicBalls.External` reached: 0. So no staged literature Prop enters Appendix A in the
  current tree.
* LatticeProb modules in the import closure: 0. This file consumes no LatticeProb.Bonanno code, so no Bonanno credit line is
  required in it.
* Remaining explicit premises of the Appendix A chain: none in Lean. This is a compile-level statement about the
  exports; it is not a closure claim for the numbered results (the operator decides that status).

## Export table

| Lemma | Frozen statement (Draft/SectionA.lean) | Check (AppendixInputChecks.lean) | Producer |
|---|---|---|---|
| A.1 | `ObstacleLeastSuperharmonicMajorantStmt` (48) | `appendixA1_export_check` | `obstacleLeastSuperharmonicMajorant_holds` (Proofs/SecA/ObstacleNonCoincidenceHarmonic.lean:615) |
| A.2 | `ObstacleNonCoincidenceHarmonicStmt` (62) | `appendixA2_export_check` | `obstacleNonCoincidenceHarmonic_holds` (same file:636) |
| A.3 | `ObstacleMonotoneStmt` (73) | `appendixA3_export_check` | `obstacleMonotone_holds` (Proofs/SecA/ObstacleMonotone.lean:164) |
| A.4 | `ObstacleOdometerZeroBoundaryStmt` (80) | `appendixA4_export_check` | `obstacleOdometerZeroBoundary_of_general` (Steps/SecA/ObstacleOdometerZeroBoundary.lean:46) applied to `obstacleOdometerZeroBoundaryGeneral_holds` (Proofs/Sec3/Basic.lean:199) |
| A.5 | `ObstacleConservationOfMassStmt` (90) | `appendixA5_export_check` | `obstacleConservationOfMass_holds` (Proofs/Sec3/ConservationOfMassLemma.lean:26) |
| A.6 | `ObstacleCompatibilityStmt` (105) | `appendixA6_export_check` | `obstacleCompatibility_holds` (Proofs/Sec3/ClusterCompatibility.lean:356) |
| A.6 | same | `appendixA6_steps_check` | `obstacleCompatibility_of_steps` (Steps/SecA/ObstacleCompatibility.lean:89) with the pole steps below |

The conjunction of the six statements is `appendixA_steps_check`, obtained from `appendixA_of_steps`
(Steps/SecA/AppendixA.lean) by applying the producers of its eighteen premises at their exact types:

| Premise of `appendixA_of_steps` | Producer (file:line) |
|---|---|
| `h23 : GreenFunctionBallStmt` (Prop 2.3) | `greenFunctionBall` (Steps/Sec2/GreenFunctionBall.lean:156) |
| `hW : SuperharmonicOfLaplacianLEStep` | `superharmonicOfLaplacianLEStep_holds` (Proofs/SecA/Basic.lean:468) |
| `hW' : LaplacianLEOfSuperharmonicStep` | `laplacianLEOfSuperharmonicStep_holds` (Proofs/SecA/Basic.lean:344) |
| `hLG : HasLaplacianOfLaplacianLEGEStep` | `hasLaplacianOfLaplacianLEGEStep_holds` (Proofs/SecA/Basic.lean:723) |
| `hq : GreenPotentialBallContinuousStep` | `greenPotentialBallContinuousStep_holds` (Proofs/SecA/ObstacleLeastSuperharmonicMajorant.lean:558) |
| `hΔq : GreenPotentialBallLaplacianStep` | `greenPotentialBallLaplacianStep_holds` (Proofs/Sec3/Basic.lean:53) |
| `hpole : ObstacleTendstoAtBotStep` | `obstacleTendstoAtBotStep_holds` (Proofs/SecA/Basic.lean:652) |
| `a11`-`a14` (A.1 Steps 1-4) | `obstacleLeastSuperharmonicMajorantStep{1,2,3,4}_holds` (Proofs/SecA/ObstacleLeastSuperharmonicMajorant.lean:562, 566, 570, 574) |
| `a22`, `a23` (A.2 Steps 2, 3) | `obstacleNonCoincidenceHarmonicStep{2,3}_holds` (Proofs/SecA/ObstacleNonCoincidenceHarmonic.lean:621, 625) |
| `a31` (A.3 Step 1) | `obstacleMonotoneStep1_holds` (Proofs/SecA/ObstacleMonotone.lean:156) |
| `a51`, `a52`, `a53` (A.5 Steps 1-3) | `obstacleConservationOfMassStep{1,2,3}_holds` (Proofs/Sec3/ConservationOfMass.lean:17; ConservationOfMassStep2.lean:31; ConservationOfMassStep3.lean:307) |
| `a61`, `a62` (A.6 Steps 1, 2) | `obstacleCompatibilityStep{1,2}_of_pole` (Steps/Sec3/ClusterCompatibility.lean:126, 131) applied to `obstacleCompatibilityPoleStep{1,2}_holds` (Proofs/Sec3/ClusterCompatibility.lean:172, 236) |

No existing file in `HarmonicBalls/Audit/` names an Appendix A export (grep for the export names), so typed checks were
added for all six. `Section9UniquenessChecks.lean` audits Lemma 9.1 only.

## Sign and normalization conventions (checked)

Each item was checked against the Lean definitions and against the displayed equations of the corrected draft.

* `Δ` is Mathlib's `Laplacian.laplacian` on `ℂ` (Defs/Laplacian.lean:17): the trace of the Hessian, so the standard
  `∂²_x + ∂²_y`.
* `newtonKernel x y = -(2π)⁻¹ log‖x - y‖` (Defs/Green.lean:43-44). With `greenFunction O x y = newtonKernel x y -
  I_O[newtonKernel x](y)` (Defs/Green.lean:70), `G_O(x,·) ≥ 0` off `x` and `ΔG_O(x,·) = -δ_x`
  (`GreenFunctionBallStmt`, Draft/Section2.lean:68-75). Checked as `greenFunction_sign_check`. The corrected draft's
  displayed disc Green function `G_{B_1}(0,y) = -(2π)⁻¹ log|y|` agrees.
* `HasLaplacian w μpos μneg U` means `Δw = μpos - μneg` (Defs/Laplacian.lean:72). `LaplacianLE w μ U` means `Δw ≤ μ`
  (Defs/Laplacian.lean:54). So `q_{B_R} = ∫_{B_R} G_{B_R}(y,·) μ(dy)` has `Δq = -μ` (`greenPotential_sign_check`), matching
  the corrected draft's property 2 of `q_{B_R}` ("`Δq_{B_R} = -μ` in `B_R`").
* `obstacle μ R z t x = -t * greenFunction (ball 0 R) z x + greenPotentialBall μ R x` (`obstacle_sign_check`, by `rfl`),
  matching eq:obstacle (`β_t(x) = -tG_{B_1}(0,x) + q_{B_1}(x)`) in the corrected draft.
* `shiftedOdometer μ R z t x = shiftedLeastSupersolution μ R z t x - obstacle μ R z t x` (`shiftedOdometer_sign_check`,
  by `rfl`), matching eq:appendix-limit-odometer (`v_t = ṽ_t - β_t`).
* `shiftedSupersolutions` uses `LaplacianLE w 0` (`Δw ≤ 0`), matching eq:shifted-supersolutions. The pole constraint is
  dropped in Lean because `β_t(0) = -∞` (the corrected draft's codomain `ℝ ∪ {∞}` at eq:obstacle is a sign typo; the
  Draft docstrings already record this).
* Consistency with the statements: `A.3` (`Λ_{t₁} ⊆ Λ_{t₂}` for `t₁ ≤ t₂`) holds because `G ≥ 0` lowers the obstacle as `t`
  grows.

## Universes

None. All six statements quantify over `Measure ℂ`, `ℂ → ℝ`, `Set ℂ`, `ℝ`, `ℂ`, and the checks carry no universe
parameters (guard). The `.{u}` universes of Sections 3-4 are not in the Appendix A chain.

## Source and provenance points for the operator (not Lean failures)

1. The corrected draft `paper/lqg_harmonic_ball-corrected.tex` carries no `% CORRECTION` marker for C2, C4 or C14. It still
   prints the volume-growth upper bound as `r^{β^-}` (line 4043), the A.5 conclusion as `μ_h(Λ_t) = t` (preserved source
   line 3789) and the A.6 `t` unbound. The frozen statements apply the adopted corrections (C2: `r^{β⁺}`; C4: `μ`;
   C14: `∀ t > 0`), as listed in `~/paper-fleets/hb/CORRECTIONS-PROPOSED.md`. The corrected draft should carry these
   markers.
2. `ObstacleCompatibilityStmt` (A.6, Draft/SectionA.lean:105) has an extra hypothesis `0 < s₁` compared with the printed
   statement (preserved source lines 3851-3854, `for all s_1 ≤ R`). The Draft docstring justifies it: for `s₁ ≤ s₂ ≤ 0 < s`
   the printed claim fails (`cluster μ s₂ 0 t = ∅` while `0 ∈ cluster μ s 0 t`). I re-verified this counterexample by hand.
   FROZEN.md lists A.6 as `[C2], [C14]` only, so this restriction is not recorded as a correction. The operator should
   record it or reject it.
3. The Draft docstring line references (for example `sec:obstacle-appendix` at 3522, `eq:volume-growth` at 3526,
   `eq:obstacle` at 3551) point to the preserved arXiv source `paper/lqg_harmonic_ball.tex`. In the corrected draft the
   same labels sit at 4037, 4041 and later. The references are correct for the preserved source only.

## Citations (not premises)

The Steps and Proofs docstrings cite Armitage-Gardiner Thm 3.2.2, 3.7.5, 4.3.8 and Pon16 Prop 7.3 / Lemma 12.15. These
are comments. The Lean chain reaches no `HarmonicBalls.Proposed` or `HarmonicBalls.External` constant, so no literature
Prop is a premise of Appendix A. The displayed corrected-draft text cites AG01 Thm 4.3.8 for `Δq_{B_R} = -μ` (consistent
with `greenPotentialBallLaplacianStep_holds`).

## Not claimed

* Closure of Lemmas A.1-A.6 as numbered results.
* That the frozen statements transcribe the corrected draft beyond the points above. Only the sign and normalization items and
  the A.6 hypothesis were checked against the displayed text in this round.
