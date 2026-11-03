import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep2
import HarmonicBalls.Proofs.Sec3.ConservationOfMass
import HarmonicBalls.Proofs.Sec3.Basic

/-!
# eq:laplacian-of-v and Lemma 3.2

`shiftedOdometerLaplacianGeneral_holds`: eq:laplacian-of-v (lines 3797-3803) and its general-ball form
eq:laplacian-of-v-general (lines 3840-3846), from Lemmas A.1, A.2, Prop 2.3, `Δ q_{B_R} = -μ` and Lemma A.5,
Steps 1-2. `clusterOpenLaplacian_proved`: **Lemma 3.2** (lemma:non-coincidence-open-harmonic, line 627) given I2.
-/

namespace HarmonicBalls

universe u

/-- eq:laplacian-of-v for a general radius and pole (`ShiftedOdometerLaplacianGeneral`). -/
theorem shiftedOdometerLaplacianGeneral_holds : ShiftedOdometerLaplacianGeneral :=
  shiftedOdometerLaplacianGeneral_of_steps obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleNonCoincidenceHarmonicGeneral_holds greenFunctionBall greenPotentialBallLaplacianStep_holds
    obstacleConservationOfMassStep1_holds obstacleConservationOfMassStep2_holds

/-- **Lemma 3.2** (lemma:non-coincidence-open-harmonic), with I2 (`LQGVolumeGrowthAllScalesStmt`) as the only
hypothesis. -/
theorem clusterOpenLaplacian_proved (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : ClusterOpenLaplacianStmt.{u} :=
  clusterOpenLaplacian_of_steps hI2 greenFunctionBall obstacleNonCoincidenceHarmonicGeneral_holds
    shiftedOdometerLaplacianGeneral_holds obstacleCompatibilityShiftStep_holds

end HarmonicBalls
