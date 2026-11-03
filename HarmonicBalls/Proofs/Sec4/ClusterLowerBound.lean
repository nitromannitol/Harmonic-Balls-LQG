import HarmonicBalls.Proofs.Sec3.Assembly
import HarmonicBalls.Steps.Sec4.ClusterLowerBound

/-!
# Proposition 4.1 (prop:lower-bound)

`clusterLowerBound_proved`: Proposition 4.1 given I2, from Prop 2.3, Lemmas 3.1, 3.2, 3.4, Lemma A.1 (general form),
the shift step, the continuity of `q_{B_R}` and Lemma A.5, Step 3 (whose equality case is the repair of gap G3).
`clusterLowerBound_of_literature`: the same from the staged literature inputs (I2 by
`lqgVolumeGrowthAllScalesStmt_of_literature`, worker c2).
-/

namespace HarmonicBalls

universe u

/-- **Proposition 4.1** (prop:lower-bound), with I2 (`LQGVolumeGrowthAllScalesStmt`) as the only hypothesis. -/
theorem clusterLowerBound_proved (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : ClusterLowerBoundStmt.{u} :=
  clusterLowerBound_of_steps hI2 greenFunctionBall (leastSupersolutionMem_proved hI2)
    (clusterOpenLaplacian_proved hI2) (clusterConservationOfMass_proved hI2)
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    greenPotentialBallContinuousStep_holds obstacleConservationOfMassStep3_holds

section FromLiterature


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

/-- **Proposition 4.1** (prop:lower-bound) from the staged literature inputs. -/
theorem clusterLowerBound_of_literature : ClusterLowerBoundStmt.{u} :=
  clusterLowerBound_proved (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN)

end FromLiterature

end HarmonicBalls
