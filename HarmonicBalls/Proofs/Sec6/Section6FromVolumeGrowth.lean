import HarmonicBalls.Proofs.Sec6.VolumeGrowthNonatomic
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! # Section 6 from all-scales volume growth

The annulus iteration uses Leonardo Bonanno's proof of the Gwynne–Miller lemma
in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The staged hypotheses
remain subject to source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory

universe u

/-- The frozen Section 6 statements follow from all-scales volume growth and
explicit affine, coordinate-change and existence hypotheses. Weyl scaling
follows from the vague-limit definition.
Non-atomicity and full support are consequences of volume growth here. -/
theorem section6_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) :
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
  exact ⟨harnackTypeEstimateStmt_of_volumeGrowth_and_affine hgrowth hAff hCC hE hW,
    harnackTypeComponentStmt_of_volumeGrowth_and_affine hgrowth hAff hCC hE hW,
    manyGoodAnnuliStmt_of_volumeGrowth hgrowth hAff hCC hE hW,
    goodAnnulusProbabilityStmt_of_volumeGrowth hgrowth hAff hCC hE hW,
    annulusIterationStmt_proved,
    manyVeryGoodAnnuliStmt_of_volumeGrowth hgrowth hAff hCC hE hW,
    veryGoodAnnulusProbabilityStmt_of_volumeGrowth hgrowth hAff hCC hE hW,
    annulusMassBoundByOdometer_of_volumeGrowth hgrowth,
    odometerHarmonicMeasureBoundStmt_of_volumeGrowth hgrowth,
    odometerBoundByAnnulusMass_of_volumeGrowth hgrowth,
    veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hgrowth,
    shellDecompositionStmt_proved, lowMassSmallOdometerStmt_of_volumeGrowth hgrowth⟩

end HarmonicBalls.Section6
