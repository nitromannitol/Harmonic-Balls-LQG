import HarmonicBalls.Proofs.Sec4.ClusterLowerBound
import HarmonicBalls.Proofs.Sec4.GreenRepresentation
import HarmonicBalls.Steps.Sec4.GreenPotentialBallHolder

/-!
# Lemma 4.2 (odometer:cont, corrected form [C8])

`leastSupersolutionHolder_proved`: Lemma 4.2 given I2, from Lemmas 3.1, 3.2, 3.4, the Green representation on a disc
(`greenRepresentationBallStep_holds`, Proofs/Sec4/GreenRepresentation.lean) and the quantitative Prop 2.5
(`greenPotentialBallHolderStep`, Steps/Sec4/GreenPotentialBallHolder.lean; gap G4).
`leastSupersolutionHolder_of_literature`: the same from the staged literature inputs.
-/

namespace HarmonicBalls

universe u

/-- **Lemma 4.2** (odometer:cont, [C8]), with I2 (`LQGVolumeGrowthAllScalesStmt`) as the only hypothesis. -/
theorem leastSupersolutionHolder_proved (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    LeastSupersolutionHolderStmt.{u} :=
  leastSupersolutionHolder_of_steps hI2 (leastSupersolutionMem_proved hI2) (clusterOpenLaplacian_proved hI2)
    (clusterConservationOfMass_proved hI2) greenRepresentationBallStep_holds greenPotentialBallHolderStep

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

/-- **Lemma 4.2** (odometer:cont, [C8]) from the staged literature inputs. -/
theorem leastSupersolutionHolder_of_literature : LeastSupersolutionHolderStmt.{u} :=
  leastSupersolutionHolder_proved (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN)

end FromLiterature

end HarmonicBalls
