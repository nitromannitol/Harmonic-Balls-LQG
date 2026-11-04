import HarmonicBalls.Proofs.Sec6.GoodPrevalenceDisc
import HarmonicBalls.Proofs.Sec6.AvoidanceBallSubmean

/-! # Good-annulus prevalence from the ball-submean estimate

The very-good-annulus reduction uses Leonardo Bonanno's Gwynne–Miller lemma
in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped ENNReal

universe u

/-- Good-annulus prevalence follows from the explicit LQG hypotheses. -/
theorem goodAnnuliSubRangeStep_of_disc
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc) : GoodAnnuliSubRangeStep.{u} := by
  obtain ⟨C, hC0, hCtop, hsubmean⟩ := unit_goodAnnulus_avoidance_ball_submean
  exact goodAnnuliSubRangeStep_of_disc_and_submean
    hholder hfull hgrowth hatom hAff hCC hC0 hCtop hsubmean

/-- The frozen good-annulus probability statement follows from the explicit LQG hypotheses. -/
theorem goodAnnulusProbabilityStmt_of_disc
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} := by
  obtain ⟨C, hC0, hCtop, hsubmean⟩ := unit_goodAnnulus_avoidance_ball_submean
  exact goodAnnulusProbabilityStmt_of_disc_and_submean
    hholder hfull hgrowth hatom hAff hCC hC0 hCtop hsubmean hex hW

/-- The frozen very-good-annulus probability statement follows from the explicit LQG hypotheses. -/
theorem veryGoodAnnulusProbabilityStmt_of_disc
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc) : VeryGoodAnnulusProbabilityStmt.{u} := by
  obtain ⟨C, hC0, hCtop, hsubmean⟩ := unit_goodAnnulus_avoidance_ball_submean
  exact veryGoodAnnulusProbabilityStmt_of_disc_and_submean
    hholder hfull hgrowth hatom hAff hCC hC0 hCtop hsubmean hex hW

end HarmonicBalls.Section6
