import HarmonicBalls.Proofs.Sec6.GoodPrevalenceVolumeGrowth
import HarmonicBalls.Proofs.Sec6.Section6VolumeGrowthAssembly

/-! # Non-atomicity and annulus prevalence from volume growth

The very-good-annulus reduction uses Leonardo Bonanno's Gwynne–Miller lemma
in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

universe u

/-- The all-scales LQG volume bound implies non-atomicity. -/
theorem lqgMeasureNonatomic_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureNonatomic P γ α₀ hC hcirc := by
  intro hGFF hγ hγ2 hα μ hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hV
  intro x
  have hR : 0 < ‖x‖ + 1 := by positivity
  have hx : x ∈ ball (0 : ℂ) (‖x‖ + 1) := by
    simp only [mem_ball, dist_zero_right]
    linarith
  exact (hV.2 _ hR).measure_singleton hx

/-- Good-annulus subrange prevalence from volume growth and the staged affine
and coordinate-change properties. -/
theorem goodAnnuliSubRangeStep_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc) : GoodAnnuliSubRangeStep.{u} :=
  goodAnnuliSubRangeStep_of_disc_volumeGrowth hgrowth
    (fun _Ω _ P γ hC hcirc => lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc)
    hAff hCC

/-- The frozen good-annulus probability statement follows from the explicit LQG hypotheses. -/
theorem goodAnnulusProbabilityStmt_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
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
  exact goodAnnulusProbabilityStmt_of_disc_volumeGrowth hgrowth
    (fun _Ω _ P γ hC hcirc => lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc)
    hAff hCC hex hW

/-- The frozen very-good-annulus probability statement follows from the explicit LQG hypotheses. -/
theorem veryGoodAnnulusProbabilityStmt_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
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
  exact veryGoodAnnulusProbabilityStmt_of_disc_volumeGrowth hgrowth
    (fun _Ω _ P γ hC hcirc => lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc)
    hAff hCC hex hW



/-- Very-good-annulus subrange prevalence from the explicit regularity and
affine-law hypotheses. -/
theorem veryGoodAnnuliSubRangeStep_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc) : VeryGoodAnnuliSubRangeStep.{u} :=
  veryGoodAnnuliSubRangeStep_of_goodAnnuliSubRangeStep (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth) hgrowth
    (goodAnnuliSubRangeStep_of_volumeGrowth hgrowth hAff hCC)
    (fun _Ω _ P γ hC hcirc => lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc) hAff hCC

/-- Lemma 6.3 follows under the explicit staged LQG hypotheses. -/
theorem manyGoodAnnuliStmt_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
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
      LQGMeasureWeylScaling P γ 0 hC hcirc) : ManyGoodAnnuliStmt.{u} :=
  manyGoodAnnuliStmt_of_literature
    (goodAnnuliSubRangeStep_of_volumeGrowth hgrowth hAff hCC) hex hW

/-- Lemma 6.6 follows under the explicit staged LQG hypotheses. -/
theorem manyVeryGoodAnnuliStmt_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
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
      LQGMeasureWeylScaling P γ 0 hC hcirc) : ManyVeryGoodAnnuliStmt.{u} :=
  manyVeryGoodAnnuliStmt_of_literature
    (veryGoodAnnuliSubRangeStep_of_volumeGrowth hgrowth hAff hCC) hex hW

/-- Proposition 6.2 follows under the explicit staged LQG hypotheses. -/
theorem harnackTypeComponentStmt_of_volumeGrowth_and_affine
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
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
      LQGMeasureWeylScaling P γ 0 hC hcirc) : HarnackTypeComponentStmt.{u} :=
  harnackTypeComponentStmt_of_volumeGrowth_and_prevalence hgrowth
    (veryGoodAnnuliSubRangeStep_of_volumeGrowth hgrowth hAff hCC) hex hW

/-- Proposition 6.1 follows under the explicit staged LQG hypotheses. -/
theorem harnackTypeEstimateStmt_of_volumeGrowth_and_affine
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
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
      LQGMeasureWeylScaling P γ 0 hC hcirc) : HarnackTypeEstimateStmt.{u} :=
  harnackTypeEstimateStmt_of_volumeGrowth_and_prevalence hgrowth
    (veryGoodAnnuliSubRangeStep_of_volumeGrowth hgrowth hAff hCC) hex hW



end HarmonicBalls.Section6
