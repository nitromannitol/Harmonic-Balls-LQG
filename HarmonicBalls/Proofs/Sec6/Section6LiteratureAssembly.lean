import HarmonicBalls.Proofs.Sec2.Assembly
import HarmonicBalls.Proofs.Sec6.ExplicitInputAssembly
import HarmonicBalls.Proofs.Sec6.GoodPrevalenceBall
import HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer
import HarmonicBalls.Proofs.Sec6.ShellDecomposition

/-! # Section 6 from the Green-potential result and staged LQG inputs

The annulus iteration uses Leonardo Bonanno's proof of the Gwynne–Miller
lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6` through
`AnnulusLawTransfer`. The staged hypotheses remain subject to source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory

universe u

/-- All frozen numbered statements in Section 6 follow from the Green-potential
clause of Proposition 2.5 and the explicitly staged whole-plane LQG inputs.
Volume growth and full support are supplied by the Section 2 assembly. -/
theorem section6_of_greenPotential_and_literature
    (hholder : GreenPotentialHolderStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ α₀ hC hcirc) :
    HarnackTypeEstimateStmt.{u} ∧ HarnackTypeComponentStmt.{u} ∧
    ManyGoodAnnuliStmt.{u} ∧ GoodAnnulusProbabilityStmt.{u} ∧
    AnnulusIterationStmt.{u} ∧ ManyVeryGoodAnnuliStmt.{u} ∧
    VeryGoodAnnulusProbabilityStmt.{u} ∧ AnnulusMassBoundByOdometerStmt.{u} ∧
    OdometerHarmonicMeasureBoundStmt.{u} ∧ OdometerBoundByAnnulusMassStmt.{u} ∧
    VeryGoodAnnulusHarnackTypeStmt.{u} ∧ ShellDecompositionStmt ∧
    LowMassSmallOdometerStmt.{u} := by
  have hgrowth := lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth
  have hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc := fun Ω _ P γ hC hcirc => hN Ω P γ 0 hC hcirc
  exact ⟨harnackTypeEstimateStmt_of_disc hholder hfull hgrowth hatom hAff hCC hE hW,
    harnackTypeComponentStmt_of_disc hholder hfull hgrowth hatom hAff hCC hE hW,
    manyGoodAnnuliStmt_of_disc hholder hfull hgrowth hatom hAff hCC hE hW,
    goodAnnulusProbabilityStmt_of_disc hholder hfull hgrowth hatom hAff hCC hE hW,
    annulusIterationStmt_proved,
    manyVeryGoodAnnuliStmt_of_disc hholder hfull hgrowth hatom hAff hCC hE hW,
    veryGoodAnnulusProbabilityStmt_of_disc hholder hfull hgrowth hatom hAff hCC hE hW,
    annulusMassBoundByOdometer_of_volumeGrowth hgrowth,
    odometerHarmonicMeasureBoundStmt_of_volumeGrowth hgrowth,
    odometerBoundByAnnulusMass_of_volumeGrowth hgrowth,
    veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hgrowth,
    shellDecompositionStmt_proved, lowMassSmallOdometerStmt_of_volumeGrowth hgrowth⟩

end HarmonicBalls.Section6
