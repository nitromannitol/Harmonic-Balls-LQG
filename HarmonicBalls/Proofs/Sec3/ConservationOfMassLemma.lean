import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep3

/-!
# Lemma A.5 and Lemma 3.4 (conservation of mass)

`obstacleConservationOfMassGeneral_holds`: Lemma A.5 for a general radius and pole (with the identity
`t = μ(Λ_t) + ν(∂Λ_t)` of lines 3822-3825), from Lemmas A.1, A.2, A.4, Prop 2.3, the shared steps and Lemma A.5,
Steps 1-3. `obstacleConservationOfMass_holds`: Lemma A.5 as printed (`ObstacleConservationOfMassStmt`).
`clusterConservationOfMass_proved`: **Lemma 3.4** (lemma:conservation-of-mass, correction C4) given I2.
-/

namespace HarmonicBalls

universe u

/-- **Lemma A.5**, general radius and pole (`ObstacleConservationOfMassGeneral`). -/
theorem obstacleConservationOfMassGeneral_holds : ObstacleConservationOfMassGeneral :=
  obstacleConservationOfMassGeneral_of_steps obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleNonCoincidenceHarmonicGeneral_holds obstacleOdometerZeroBoundaryGeneral_holds greenFunctionBall
    greenPotentialBallContinuousStep_holds greenPotentialBallLaplacianStep_holds
    obstacleConservationOfMassStep1_holds obstacleConservationOfMassStep2_holds
    obstacleConservationOfMassStep3_holds

/-- **Lemma A.5** (lemma:appendix-conservation-of-mass) as printed (`ObstacleConservationOfMassStmt`). -/
theorem obstacleConservationOfMass_holds : ObstacleConservationOfMassStmt :=
  obstacleConservationOfMass_of_general obstacleConservationOfMassGeneral_holds

/-- **Lemma 3.4** (lemma:conservation-of-mass), with I2 (`LQGVolumeGrowthAllScalesStmt`) as the only hypothesis. -/
theorem clusterConservationOfMass_proved (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ClusterConservationOfMassStmt.{u} :=
  clusterConservationOfMass_of_steps hI2 obstacleOdometerZeroBoundaryGeneral_holds
    obstacleConservationOfMassGeneral_holds obstacleCompatibilityShiftStep_holds

end HarmonicBalls
