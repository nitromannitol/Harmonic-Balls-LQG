import HarmonicBalls.Steps.SecA.ObstacleConservationOfMass
import HarmonicBalls.Steps.SecA.ObstacleMonotone
import HarmonicBalls.Steps.SecA.ObstacleCompatibility

/-!
# Appendix A from its steps

The six statements of Appendix A (Lemmas A.1-A.6, Draft/SectionA.lean) from the leaves of the carving and
Prop 2.3 (`GreenFunctionBallStmt`, Draft/Section2.lean), the only numbered input from outside Appendix A.

| leaf | file | claim | difficulty |
|---|---|---|---|
| `SuperharmonicOfLaplacianLEStep` | Basic | continuous, `Δw ≤ 0` distributionally ⇒ classically superharmonic | medium-hard |
| `LaplacianLEOfSuperharmonicStep` | Basic | continuous, classically superharmonic ⇒ `Δw ≤ 0` | medium |
| `HasLaplacianOfLaplacianLEGEStep` | Basic | `Δw ≤ 0` and `Δw ≥ 0` ⇒ `Δw = 0` | easy-medium |
| `GreenPotentialBallContinuousStep` | Basic | `q_{B_R}` continuous on the closed ball | medium-hard |
| `GreenPotentialBallLaplacianStep` | Basic | `Δ q_{B_R} = -μ` on `B_R` (AG01 Thm 4.3.8) | hard |
| `ObstacleTendstoAtBotStep` | Basic | `β_t → -∞` at the pole | easy |
| `ObstacleLeastSuperharmonicMajorantStep1` | A.1 | superharmonic majorants are `≥ 0` (minimum principle) | medium |
| `ObstacleLeastSuperharmonicMajorantStep2` | A.1 | `f_t` superharmonic (AG01 Thm 3.7.5) | hard |
| `ObstacleLeastSuperharmonicMajorantStep3` | A.1 | `f_t` usc off the pole (Poisson modification) | hard |
| `ObstacleLeastSuperharmonicMajorantStep4` | A.1 | `f_t` usc at the pole (gap G2) | medium |
| `ObstacleNonCoincidenceHarmonicStep2` | A.2 | `ṽ_t` subharmonic on `Λ_t` | hard |
| `ObstacleNonCoincidenceHarmonicStep3` | A.2 | no open `W ⊆ Λ_t` away from the pole with `∂W ∩ Λ_t = ∅` | medium |
| `ObstacleMonotoneStep1` | A.3 | truncated competitor in `S̃(t₁)` (minor gap) | medium |
| `ObstacleConservationOfMassStep1` | A.5 | `Δ v_t ≥ 0` off the pole (gap G1, repair I7) | medium |
| `ObstacleConservationOfMassStep2` | A.5 | `Δ v = -t δ_z + μ|_Λ + ν|_{∂Λ}`, `ν ≤ μ` (general `U`) | hard |
| `ObstacleConservationOfMassStep3` | A.5 | `σ(B_R) ≤ t`, equality for compact support (Pon16 7.3, 12.15) | hard |
| `ObstacleCompatibilityStep1` | A.6 | `u^{B_{r₁}} ≤ u^{B_{r₂}}` | medium |
| `ObstacleCompatibilityStep2` | A.6 | `u^{B_R} ≤ ū` (subharmonic comparison) | hard |

Auxiliary (used inside A.6 Steps 1-2 and by Section 3, not by any reduction): `ObstacleCompatibilityShiftStep`.
-/

namespace HarmonicBalls

/-- **Appendix A from its steps.** Lemmas A.1-A.6 follow from the leaves of the carving and Prop 2.3. -/
theorem appendixA_of_steps (h23 : GreenFunctionBallStmt)
    (hW : SuperharmonicOfLaplacianLEStep) (hW' : LaplacianLEOfSuperharmonicStep)
    (hLG : HasLaplacianOfLaplacianLEGEStep) (hq : GreenPotentialBallContinuousStep)
    (hΔq : GreenPotentialBallLaplacianStep) (hpole : ObstacleTendstoAtBotStep)
    (a11 : ObstacleLeastSuperharmonicMajorantStep1) (a12 : ObstacleLeastSuperharmonicMajorantStep2)
    (a13 : ObstacleLeastSuperharmonicMajorantStep3) (a14 : ObstacleLeastSuperharmonicMajorantStep4)
    (a22 : ObstacleNonCoincidenceHarmonicStep2) (a23 : ObstacleNonCoincidenceHarmonicStep3)
    (a31 : ObstacleMonotoneStep1) (a51 : ObstacleConservationOfMassStep1)
    (a52 : ObstacleConservationOfMassStep2) (a53 : ObstacleConservationOfMassStep3)
    (a61 : ObstacleCompatibilityStep1) (a62 : ObstacleCompatibilityStep2) :
    ObstacleLeastSuperharmonicMajorantStmt ∧ ObstacleNonCoincidenceHarmonicStmt ∧ ObstacleMonotoneStmt ∧
      ObstacleOdometerZeroBoundaryStmt ∧ ObstacleConservationOfMassStmt ∧ ObstacleCompatibilityStmt := by
  have hA1 := obstacleLeastSuperharmonicMajorantGeneral_of_steps hW hW' hq hΔq a11 a12 a13 a14
  have hA2 := obstacleNonCoincidenceHarmonicGeneral_of_steps hA1 h23 hW' hLG hq hpole a22 a23
  have hA4 := obstacleOdometerZeroBoundaryGeneral_of_steps hq hΔq
  exact ⟨obstacleLeastSuperharmonicMajorant_of_general hA1, obstacleNonCoincidenceHarmonic_of_general hA2,
    obstacleMonotone_of_steps a31, obstacleOdometerZeroBoundary_of_general hA4,
    obstacleConservationOfMass_of_steps hA1 hA2 hA4 h23 hq hΔq a51 a52 a53,
    obstacleCompatibility_of_steps a61 a62⟩

end HarmonicBalls
