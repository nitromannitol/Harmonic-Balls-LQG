import HarmonicBalls.Proofs.Sec6.Section6FromVolumeGrowth
import HarmonicBalls.Proofs.Sec2.Assembly
import HarmonicBalls.Proofs.Sec6.NonpositiveSingularityNonatomic

/-! # Section 6 from staged literature inputs

The annulus iteration uses Leonardo Bonanno's proof of the Gwynne–Miller lemma
in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The literature inputs
below are explicit hypotheses and remain subject to operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory

universe u

/-- The Section 6 statements follow from the staged whole-plane ball-mass,
affine-invariance, coordinate-change, existence, and non-atomicity inputs
for positive singularity strengths. Weyl scaling is derived from vague
convergence, and nonpositive singularities are handled by local comparison;
the intermediate all-scales
volume growth is supplied by the Section 2 reduction. -/
theorem section6_of_literature_without_weyl
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      0 < α₀ → LQGMeasureNonatomic P γ α₀ hC hcirc) :
    HarnackTypeEstimateStmt.{u} ∧ HarnackTypeComponentStmt.{u} ∧
    ManyGoodAnnuliStmt.{u} ∧ GoodAnnulusProbabilityStmt.{u} ∧
    AnnulusIterationStmt.{u} ∧ ManyVeryGoodAnnuliStmt.{u} ∧
    VeryGoodAnnulusProbabilityStmt.{u} ∧ AnnulusMassBoundByOdometerStmt.{u} ∧
    OdometerHarmonicMeasureBoundStmt.{u} ∧ OdometerBoundByAnnulusMassStmt.{u} ∧
    VeryGoodAnnulusHarnackTypeStmt.{u} ∧ ShellDecompositionStmt ∧
    LowMassSmallOdometerStmt.{u} := by
  have hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  have hS : WholePlaneScaledBallMassStep.{u} :=
    wholePlaneScaledBallMassStep_of_rescaled
      (rescaledBallMassUniformStep_of_DG hDG hAff hCC wholePlaneGFFMixtureStep_holds)
  have hNall : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ α₀ hC hcirc := by
    intro Ω _ P γ α₀ hC hcirc
    by_cases hα : 0 < α₀
    · exact hN Ω P γ α₀ hC hcirc hα
    · intro hG hγ hγ2 _ μ hμ
      exact ae_singular_nonatomic_of_nonpositive hS P γ α₀ hγ hγ2 (le_of_not_gt hα)
        hC hcirc (hE Ω P γ hC hcirc) μ hG hμ
  exact section6_of_volumeGrowth
    (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hNall) hAff hCC hE

end HarmonicBalls.Section6
