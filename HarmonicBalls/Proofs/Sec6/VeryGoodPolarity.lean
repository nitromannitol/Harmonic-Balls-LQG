import HarmonicBalls.Proofs.Sec6.VeryGoodProbabilityAssembly
import HarmonicBalls.Proofs.Sec6.LogAnnulusHitting

/-! # Very-good-annulus probability with Brownian point polarity

The subrange prevalence development uses Leonardo Bonanno's proof of the
Gwynne–Miller lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter MarkovProcess
open scoped ENNReal NNReal

universe u

/-- The frozen Lemma 6.7 follows from good-annulus prevalence, volume growth
and the displayed LQG inputs. -/
theorem veryGoodAnnulusProbabilityStmt_of_subrange
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u})
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
      LQGMeasureWeylScaling P γ 0 hC hcirc) :
    VeryGoodAnnulusProbabilityStmt.{u} := by
  apply veryGoodAnnulusProbabilityStmt_of_subrange_and_point_avoidance
    hgrowth hsub hAff hCC hex hW
  intro v _ x _ hx
  exact planarBrownianMotion_point_avoidance v x hx.symm

end HarmonicBalls.Section6
