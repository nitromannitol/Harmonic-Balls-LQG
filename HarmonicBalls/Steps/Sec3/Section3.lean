import HarmonicBalls.Steps.Sec3.LeastSupersolutionMem
import HarmonicBalls.Steps.Sec3.ClusterOpenLaplacian
import HarmonicBalls.Steps.Sec3.ClusterMonotone
import HarmonicBalls.Steps.Sec3.ClusterConservationOfMass
import HarmonicBalls.Steps.Sec3.ClusterCompatibility

/-!
# Section 3.2 from its steps

Lemmas 3.1-3.5 (Draft/Section3.lean) from the leaves of the carving of Appendix A (Steps/SecA, the table of
AppendixA.lean), the substitution `ObstacleCompatibilityShiftStep` (lines 3574-3578), the two general-pole steps of
Lemma A.6 (ClusterCompatibility.lean), Prop 2.3 (`GreenFunctionBallStmt`) and Input I2
(`LQGVolumeGrowthAllScalesStmt`).

| result | reduction | consumes |
|---|---|---|
| Lemma 3.1 | `leastSupersolutionMem_of_steps` | A.1 general, shift, I2 |
| Lemma 3.2 | `clusterOpenLaplacian_of_steps` | A.2 general, eq:laplacian-of-v-general, shift, Prop 2.3, I2 |
| Lemma 3.3 | `clusterMonotone_of_steps` | A.3 general, shift, I2 |
| Lemma 3.4 | `clusterConservationOfMass_of_steps` | A.4 general, A.5 general, shift, I2 |
| Lemma 3.5 | `clusterCompatibility_of_steps` | `ObstacleCompatibilityPoleStep1/2` (A.6, pole `z`), I2 |

New leaves of this directory: `ObstacleCompatibilityPoleStep1` and `ObstacleCompatibilityPoleStep2`
which supersede the pole-`0` Steps 1-2 of Lemma A.6 (`obstacleCompatibilityStep1_of_pole`,
`obstacleCompatibilityStep2_of_pole`).
-/

namespace HarmonicBalls

universe u

/-- **Section 3.2 from its steps.** Lemmas 3.1-3.5 follow from the leaves of the carving of Appendix A (with the
general-pole steps of Lemma A.6), the substitution of lines 3574-3578, Prop 2.3 and Input I2. -/
theorem section3_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h23 : GreenFunctionBallStmt)
    (hS : ObstacleCompatibilityShiftStep)
    (hW : SuperharmonicOfLaplacianLEStep) (hW' : LaplacianLEOfSuperharmonicStep)
    (hLG : HasLaplacianOfLaplacianLEGEStep) (hq : GreenPotentialBallContinuousStep)
    (hΔq : GreenPotentialBallLaplacianStep) (hpole : ObstacleTendstoAtBotStep)
    (a11 : ObstacleLeastSuperharmonicMajorantStep1) (a12 : ObstacleLeastSuperharmonicMajorantStep2)
    (a13 : ObstacleLeastSuperharmonicMajorantStep3) (a14 : ObstacleLeastSuperharmonicMajorantStep4)
    (a22 : ObstacleNonCoincidenceHarmonicStep2) (a23 : ObstacleNonCoincidenceHarmonicStep3)
    (a31 : ObstacleMonotoneStep1) (a51 : ObstacleConservationOfMassStep1)
    (a52 : ObstacleConservationOfMassStep2) (a53 : ObstacleConservationOfMassStep3)
    (p1 : ObstacleCompatibilityPoleStep1) (p2 : ObstacleCompatibilityPoleStep2) :
    LeastSupersolutionMemStmt.{u} ∧ ClusterOpenLaplacianStmt.{u} ∧ ClusterMonotoneStmt.{u} ∧
      ClusterConservationOfMassStmt.{u} ∧ ClusterCompatibilityStmt.{u} := by
  have hA1 := obstacleLeastSuperharmonicMajorantGeneral_of_steps hW hW' hq hΔq a11 a12 a13 a14
  have hA2 := obstacleNonCoincidenceHarmonicGeneral_of_steps hA1 h23 hW' hLG hq hpole a22 a23
  have hA4 := obstacleOdometerZeroBoundaryGeneral_of_steps hq hΔq
  exact ⟨leastSupersolutionMem_of_steps hI2 hA1 hS,
    clusterOpenLaplacian_of_steps hI2 h23 hA2
      (shiftedOdometerLaplacianGeneral_of_steps hA1 hA2 h23 hΔq a51 a52) hS,
    clusterMonotone_of_steps hI2 (obstacleMonotoneGeneral_of_steps a31) hS,
    clusterConservationOfMass_of_steps hI2 hA4
      (obstacleConservationOfMassGeneral_of_steps hA1 hA2 hA4 h23 hq hΔq a51 a52 a53) hS,
    clusterCompatibility_of_steps hI2 p1 p2⟩

end HarmonicBalls
