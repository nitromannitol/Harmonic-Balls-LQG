import HarmonicBalls.Draft.Section2
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.LPStage.LQGMeasureFullSupport3

/-!
# LP-stage bridge for the full support of the LQG measure (row 40, z3)

`HarmonicBalls.lqgMeasureFullSupportStmt_of_lpStage` is the HB statement `LQGMeasureFullSupportStmt`
(`HarmonicBalls/Draft/Section2.lean:109`, I1), obtained from the LP statement `LQGMeasureFullSupportStmtLP`
(`LPStage/LQGMeasureFullSupport.lean`) through the bridge equivalences `isWholePlaneGFF_iff` (M1) and
`isLQGMeasureOfField_iff` (M4); the conclusion is the same Prop on both sides.

The LP-stage proof is `LatticeProb.LQG.lqgMeasureFullSupportStmt_of_scaled_lp` (`LPStage/LQGMeasureFullSupport3.lean`),
fed by the LP scaled step `WholePlaneScaledBallMassStepLP` (derived from the inputs by the proved LP lemmas
`rescaledBallMassUniformStep_lp`, `wholePlaneScaledBallMassStep_of_uniform_lp`, `circleAverageDyadicTailStep_lp`),
the non-atomicity `lqgMeasureNonatomic_lp` and the existence `LQGMeasureExistenceLP` at `α₀ = 0`. The three LP
literature inputs `WholePlaneLQGBallMassBoundsLP`, `LQGMeasureCoordChangeLP` and `LQGMeasureExistenceLP` are
hypotheses of the bridge (R54): they are not proved here and remain pending the operator's source check of their
Proposed counterparts.
-/

namespace HarmonicBalls

open MeasureTheory
open LPBridge

universe u

/-- Row 40 in HB form: `LQGMeasureFullSupportStmt` (I1, full support of `μ_h`) from the LP literature inputs. -/
theorem lqgMeasureFullSupportStmt_of_lpStage
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.WholePlaneLQGBallMassBoundsLP P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.LQGMeasureCoordChangeLP P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.LQGMeasureExistenceLP P γ α hC hcirc) :
    LQGMeasureFullSupportStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hS : LatticeProb.LQG.LQGMeasureNonatomicMass.WholePlaneScaledBallMassStepLP.{u} :=
    LatticeProb.LQG.LQGMeasureNonatomicMass.wholePlaneScaledBallMassStep_of_uniform_lp
      (LatticeProb.LQG.LQGMeasureNonatomicMass.rescaledBallMassUniformStep_lp hDG hCC)
      LatticeProb.LQG.LQGMeasureNonatomicMass.circleAverageDyadicTailStep_lp
  have hFull : LatticeProb.LQG.LQGMeasureFullSupportStmtLP.{u} :=
    LatticeProb.LQG.lqgMeasureFullSupportStmt_of_scaled_lp.{u} hS
      (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) (LatticeProb.LQG.lqgMeasureNonatomic_lp hDG hCC hE)
  filter_upwards [hFull γ α₀ hγ hγ2 hα Ω P hC hcirc μ ((isWholePlaneGFF_iff P hC hcirc).1 hGFF)
    ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ)] with ω hω
  exact hω

end HarmonicBalls
