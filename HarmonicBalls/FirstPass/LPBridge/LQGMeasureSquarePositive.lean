import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.LQGMeasureSquarePositive

/-!
# LP-stage bridge for the square positivity of the LQG measure

`HarmonicBalls.lqgMeasureSquarePositiveFrozen_of_lpStage` is the HB statement `LQGMeasureSquarePositiveFrozen`
(`FirstPass/Frozen/S11c.lean:130`), obtained from the LP statement `LQGMeasureSquarePositiveLP`
(`LPStage/LQGMeasureSquarePositive.lean`) through the bridge equivalences `isWholePlaneGFF_iff` (M1) and
`isLQGMeasureOfField_iff` (M4). The HB and LP definitions of `IsClosedDyadicSquare` agree by unfolding.

The LP-stage proof is `LatticeProb.LQG.lqgMeasureSquarePositiveLP_of_inputs`, from the three LP literature inputs
`WholePlaneLQGBallMassBoundsLP`, `LQGMeasureCoordChangeLP` and `LQGMeasureExistenceLP` (the binders of the HB
derivation `HarmonicBalls.lqgMeasureSquarePositiveFrozen_derived`, `FirstPass/Phase2/SquarePositiveDerived.lean:40`).
These inputs are hypotheses of the bridge: they are not proved here and remain pending the operator's source
check of their Proposed counterparts.
-/

namespace HarmonicBalls

open MeasureTheory
open LPBridge

universe u

/-- Row 23 in HB form: `LQGMeasureSquarePositiveFrozen` (every closed dyadic square has positive LQG mass a.s.) from the
LP literature inputs. -/
theorem lqgMeasureSquarePositiveFrozen_of_lpStage
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.WholePlaneLQGBallMassBoundsLP P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.LQGMeasureCoordChangeLP P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.LQGMeasureExistenceLP P γ α hC hcirc) :
    LQGMeasureSquarePositiveFrozen.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ S hS
  exact LatticeProb.LQG.lqgMeasureSquarePositiveLP_of_inputs hDG hCC hE γ α₀ hγ hγ2 hα Ω P hC hcirc μ
    ((isWholePlaneGFF_iff P hC hcirc).1 hGFF) ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ) S hS

end HarmonicBalls
