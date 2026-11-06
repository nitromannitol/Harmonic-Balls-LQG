import HarmonicBalls.Proofs.Sec1.LocalityCompatibilityAssembly
import HarmonicBalls.Proofs.Sec5.ExistenceFromVolumeGrowth
import HarmonicBalls.Proofs.Sec5.NoEntryPropagation
import HarmonicBalls.Proofs.Sec10.JordanIntegerRadii
import HarmonicBalls.Proofs.Sec11.NotLipschitz
import HarmonicBalls.Proofs.Sec11.NotMetricBallGrowth

/-! # Section 1 conditional interface checks

These checks retain the actual hypotheses and frozen proposition aliases.
They do not assert closure of any numbered result. The imported potential
 theory includes work of Leonardo Bonanno.
-/

namespace HarmonicBalls.Section1ConditionalExportsAudit

open MeasureTheory
universe u

example (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u})
    (h58 : ClusterStrongCompatibilityStmt.{u}) (hlocal : ClusterContainmentLocalityStep.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureLocality P γ α₀ hC hcirc) : HarmonicBallLocalSetStmt.{u} :=
  harmonicBallLocalSet_of_steps h58 h55 h56 hlocal hmeasure

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u})
    (h58 : ClusterStrongCompatibilityStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureLocality P γ α₀ hC hcirc) : HarmonicBallLocalSetStmt.{u} :=
  harmonicBallLocalSet_of_volumeGrowth_and_compatibility hI2 h55 h56 h58 hmeasure

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureLocality P γ α₀ hC hcirc) : HarmonicBallLocalSetStmt.{u} :=
  harmonicBallLocalSet_of_volumeGrowth_existence_uniqueness_and_measureLocality hI2 h55 h56 hmeasure

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : ExistenceHarmonicBallsStmt.{u} :=
  existenceHarmonicBalls_of_volumeGrowth_and_clusterEstimates hI2 h53 h71 h72 hAff hCC

example (h93 : HarmonicBallBoundarySubsetStmt.{u}) (h94 : RegularOpenEqOfAEEqStmt.{u})
    (hfull : LQGMeasureFullSupportStmt.{u}) : UniquenessHarmonicBallsStmt.{u} :=
  uniquenessHarmonicBalls_of_boundary_and_fullSupport h93 h94 hfull

example (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h55 : ExistenceHarmonicBallsStmt.{u})
    (hjordan : ClusterJordanIntegerRadii.{u}) : HarmonicBallComplementBoundaryJordanStmt.{u} :=
  harmonicBallComplementBoundaryJordan_of_volumeGrowth hI2 h55 hjordan

example (hnocone : NoConeConditionStmt.{u}) : HarmonicBallNotLipschitzStmt.{u} :=
  harmonicBallNotLipschitzStmt_of_noConeCondition hnocone

example (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : ManyPinchScalesStmt.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hmetric : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNotMetricBallStmt.{u} :=
  harmonicBallNotMetricBallStmt_of_comparison_pinch_and_volumeGrowth hbound hmany hgrowth hmetric

#print axioms harmonicBallLocalSet_of_volumeGrowth_existence_uniqueness_and_measureLocality
#print axioms existenceHarmonicBalls_of_volumeGrowth_and_clusterEstimates
#print axioms harmonicBallComplementBoundaryJordan_of_volumeGrowth
#print axioms harmonicBallNotMetricBallStmt_of_comparison_pinch_and_volumeGrowth

end HarmonicBalls.Section1ConditionalExportsAudit
