import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence
import HarmonicBalls.Proofs.Sec6.GoodAnnulusPhaseProbability
import HarmonicBalls.Proofs.Sec6.VeryGoodAllRadiiFineSupport
import HarmonicBalls.Proofs.Sec6.Section6FromVolumeGrowth

/-! # Section 6 from volume growth and zero-strength existence

The annulus iteration uses Leonardo Bonanno's proof of the Gwynne–Miller lemma
in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The zero-strength
existence input is staged and remains subject to operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory

universe u

/-- The frozen Section 6 statements follow from all-scales volume growth and
zero-strength LQG measure existence. -/
theorem section6_of_volumeGrowth_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) :
    HarnackTypeEstimateStmt.{u} ∧ HarnackTypeComponentStmt.{u} ∧
    ManyGoodAnnuliStmt.{u} ∧ GoodAnnulusProbabilityStmt.{u} ∧
    AnnulusIterationStmt.{u} ∧ ManyVeryGoodAnnuliStmt.{u} ∧
    VeryGoodAnnulusProbabilityStmt.{u} ∧ AnnulusMassBoundByOdometerStmt.{u} ∧
    OdometerHarmonicMeasureBoundStmt.{u} ∧ OdometerBoundByAnnulusMassStmt.{u} ∧
    VeryGoodAnnulusHarnackTypeStmt.{u} ∧ ShellDecompositionStmt ∧
    LowMassSmallOdometerStmt.{u} := by
  exact ⟨harnackTypeEstimateStmt_of_volumeGrowth_zero_existence hgrowth hE0,
    harnackTypeComponentStmt_of_volumeGrowth_zero_existence hgrowth hE0,
    manyGoodAnnuliStmt_of_volumeGrowth_zero_existence hgrowth hE0,
    goodAnnulusProbabilityStmt_of_volumeGrowth_zero_existence hgrowth hE0,
    annulusIterationStmt_proved,
    manyVeryGoodAnnuliStmt_of_volumeGrowth_zero_existence hgrowth hE0,
    veryGoodAnnulusProbabilityStmt_of_volumeGrowth_zero_existence hgrowth hE0,
    annulusMassBoundByOdometer_of_volumeGrowth hgrowth,
    odometerHarmonicMeasureBoundStmt_of_volumeGrowth hgrowth,
    odometerBoundByAnnulusMass_of_volumeGrowth hgrowth,
    veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hgrowth,
    shellDecompositionStmt_proved, lowMassSmallOdometerStmt_of_volumeGrowth hgrowth⟩

end HarmonicBalls.Section6
