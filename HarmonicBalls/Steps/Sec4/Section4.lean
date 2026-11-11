import HarmonicBalls.Steps.Sec4.ClusterLowerBound
import HarmonicBalls.Steps.Sec4.LeastSupersolutionHolder
import HarmonicBalls.Steps.Sec4.ClusterSubharmonicBall
import HarmonicBalls.Steps.Sec3.Section3

/-!
# Section 4 from its steps

Proposition 4.1 and Lemmas 4.2-4.3 (Draft/Section4.lean) from the statements of Sections 2-3, steps of Appendix A
and the new steps of this directory.

| result | reduction | consumes |
|---|---|---|
| Prop 4.1 | `clusterLowerBound_of_steps` | I2, Prop 2.3, Lemmas 3.1, 3.2, 3.4, A.1 general, shift, `GreenPotentialBallContinuousStep`, A.5 Step 3 |
| Lemma 4.2 | `leastSupersolutionHolder_of_steps` | I2, Lemmas 3.1, 3.2, 3.4, `GreenRepresentationBallStep`, `GreenPotentialBallHolderStep` |
| Lemma 4.3 | `clusterSubharmonicBall_of_steps` | I2, Prop 2.3, Lemmas 3.1, 3.2, 3.4, `GreenRepresentationBallStep`, `ClusterHarmonicQuadratureStep`, `ClusterGreenPotentialIdentityStep`, `GreenFunctionIntegrableAwayFromPoleStep` |

## New leaves of this directory

| step | file | paper | difficulty |
|---|---|---|---|
| `GreenPotentialBallHolderStep` | GreenPotentialBallHolderStep.lean | Prop 2.5 quantitative | **proved** (GreenPotentialBallHolder.lean) |
| `GreenRepresentationBallStep` | LeastSupersolutionHolder.lean | line 732 (implicit; Riesz decomposition) | **proved** (Proofs/Sec4/GreenRepresentation.lean) |
| `ClusterHarmonicQuadratureStep` | ClusterSubharmonicBall.lean | lines 773-779 | **proved** (Proofs/Sec4/ClusterSubharmonicBall.lean) |
| `ClusterGreenPotentialIdentityStep` | ClusterSubharmonicBall.lean | lines 781-786 | **proved** from the next step and Step 1 (Proofs/Sec4/ClusterGreenIdentity.lean) |
| `GreenHarmonicCorrectionBalayageStep` | ClusterSubharmonicBall.lean | Green function of a general open set | **proved** (Proofs/Sec4/GreenBalayage.lean, sweeping: Proofs/Sec4/Sweep.lean) |
| `GreenFunctionIntegrableAwayFromPoleStep` | ClusterSubharmonicBall.lean | implicit (ν₁-integrability) | **proved** (Proofs/Sec4/GreenAwayFromPole.lean) |

The last claim of Prop 4.1 needs no new leaf: it is the equality case of `ObstacleConservationOfMassStep3`
(Lemma A.5, Step 3), which does not assume `μ_h(∂Λ) = 0`.

`GreenPotentialBallHolderStep` is proved in GreenPotentialBallHolder.lean, which cannot be imported here: the name
`HarmonicBalls.continuousOn_greenFunction_ball` is declared both in Steps/SecA/Basic.lean and in
Proofs/Potential/GreenBall.lean. Renaming one of them makes `section4_of_leaves` free of that hypothesis.
-/

namespace HarmonicBalls

universe u

/-- **Section 4 from the statements of Sections 2-3 and the steps.** -/
theorem section4_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h23 : GreenFunctionBallStmt)
    (h31 : LeastSupersolutionMemStmt.{u}) (h32 : ClusterOpenLaplacianStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hS : ObstacleCompatibilityShiftStep) (hq : GreenPotentialBallContinuousStep)
    (a53 : ObstacleConservationOfMassStep3) (hRep : GreenRepresentationBallStep)
    (hHol : GreenPotentialBallHolderStep) (hS1 : ClusterHarmonicQuadratureStep)
    (hS2 : ClusterGreenPotentialIdentityStep) (hS3 : GreenFunctionIntegrableAwayFromPoleStep) :
    ClusterLowerBoundStmt.{u} ∧ LeastSupersolutionHolderStmt.{u} ∧ ClusterSubharmonicBallStmt.{u} :=
  ⟨clusterLowerBound_of_steps hI2 h23 h31 h32 h34 hA1 hS hq a53,
    leastSupersolutionHolder_of_steps hI2 h31 h32 h34 hRep hHol,
    clusterSubharmonicBall_of_steps hI2 h23 h31 h32 h34 hRep hS1 hS2 hS3⟩

/-- **Section 4 from the leaves.** Proposition 4.1 and Lemmas 4.2-4.3 from the leaves of the carving of Appendix A
(those of `section3_of_steps`) and the new leaves of this directory. -/
theorem section4_of_leaves (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h23 : GreenFunctionBallStmt)
    (hS : ObstacleCompatibilityShiftStep)
    (hW : SuperharmonicOfLaplacianLEStep) (hW' : LaplacianLEOfSuperharmonicStep)
    (hLG : HasLaplacianOfLaplacianLEGEStep) (hq : GreenPotentialBallContinuousStep)
    (hΔq : GreenPotentialBallLaplacianStep) (hpole : ObstacleTendstoAtBotStep)
    (a11 : ObstacleLeastSuperharmonicMajorantStep1) (a12 : ObstacleLeastSuperharmonicMajorantStep2)
    (a13 : ObstacleLeastSuperharmonicMajorantStep3) (a14 : ObstacleLeastSuperharmonicMajorantStep4)
    (a22 : ObstacleNonCoincidenceHarmonicStep2) (a23 : ObstacleNonCoincidenceHarmonicStep3)
    (a31 : ObstacleMonotoneStep1) (a51 : ObstacleConservationOfMassStep1)
    (a52 : ObstacleConservationOfMassStep2) (a53 : ObstacleConservationOfMassStep3)
    (p1 : ObstacleCompatibilityPoleStep1) (p2 : ObstacleCompatibilityPoleStep2)
    (hRep : GreenRepresentationBallStep) (hHol : GreenPotentialBallHolderStep)
    (hS1 : ClusterHarmonicQuadratureStep) (hS2 : ClusterGreenPotentialIdentityStep)
    (hS3 : GreenFunctionIntegrableAwayFromPoleStep) :
    ClusterLowerBoundStmt.{u} ∧ LeastSupersolutionHolderStmt.{u} ∧ ClusterSubharmonicBallStmt.{u} := by
  obtain ⟨h31, h32, -, h34, -⟩ := section3_of_steps hI2 h23 hS hW hW' hLG hq hΔq hpole a11 a12 a13 a14 a22 a23
    a31 a51 a52 a53 p1 p2
  exact section4_of_steps hI2 h23 h31 h32 h34
    (obstacleLeastSuperharmonicMajorantGeneral_of_steps hW hW' hq hΔq a11 a12 a13 a14) hS hq a53 hRep hHol hS1
    hS2 hS3

end HarmonicBalls
