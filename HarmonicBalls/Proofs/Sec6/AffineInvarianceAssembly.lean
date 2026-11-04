import HarmonicBalls.Proofs.Sec6.WeakerSingularityExistence
import HarmonicBalls.Proofs.Sec6.DyadicVeryGoodPrevalence
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly

/-! # Section 6 with proved affine invariance

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The remaining staged LQG
hypotheses are explicit and await source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory

universe u

/-- The good-annulus subrange step follows from volume growth and the staged
LQG coordinate-change law; GFF affine invariance is proved. -/
theorem goodAnnuliSubRangeStep_of_volumeGrowth_coordChange
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc) : GoodAnnuliSubRangeStep.{u} :=
  goodAnnuliSubRangeStep_of_volumeGrowth hgrowth
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC

/-- The very-good subrange step follows from good-annulus prevalence and volume
growth, with no additional coordinate-change hypothesis. -/
theorem veryGoodAnnuliSubRangeStep_of_goodPrevalence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u}) : VeryGoodAnnuliSubRangeStep.{u} :=
  veryGoodAnnuliSubRangeStep_of_goodPrevalence_of_translation hgrowth hsub
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc)

/-- All frozen Section 6 conclusions follow from the staged whole-plane mass
bounds, coordinate-change law, and a cofinal sequence of existence inputs. -/
theorem section6_of_massBounds_coordChange_cofinal_existence
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (n : ℕ),
      LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    HarnackTypeEstimateStmt.{u} ∧ HarnackTypeComponentStmt.{u} ∧
    ManyGoodAnnuliStmt.{u} ∧ GoodAnnulusProbabilityStmt.{u} ∧
    AnnulusIterationStmt.{u} ∧ ManyVeryGoodAnnuliStmt.{u} ∧
    VeryGoodAnnulusProbabilityStmt.{u} ∧ AnnulusMassBoundByOdometerStmt.{u} ∧
    OdometerHarmonicMeasureBoundStmt.{u} ∧ OdometerBoundByAnnulusMassStmt.{u} ∧
    VeryGoodAnnulusHarnackTypeStmt.{u} ∧ ShellDecompositionStmt ∧
    LowMassSmallOdometerStmt.{u} :=
  section6_of_cofinal_existence_alone hDG
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC hE

end HarmonicBalls.Section6
