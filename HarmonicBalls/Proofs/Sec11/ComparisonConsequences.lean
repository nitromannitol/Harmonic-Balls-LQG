import HarmonicBalls.Proofs.Sec11.AnnulusMassComparison
import HarmonicBalls.Proofs.Sec11.NotLipschitz
import HarmonicBalls.Proofs.Sec5.NoEntryPropagation
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.RegularOpenEqOfAEEq

/-! # Consequences of the annulus comparison -/

namespace HarmonicBalls

open MeasureTheory Section6

universe u

/-- The annulus mass comparison with harmonic-ball uniqueness derived from
volume growth. The affine invariance and coordinate-change hypotheses are
staged pending source review. -/
theorem annulusMassBoundByHarmonicChainStmt_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hexist : ExistenceHarmonicBallsStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : AnnulusMassBoundByHarmonicChainStmt.{u} := by
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hI2
  have hunique := uniquenessHarmonicBalls_of_boundary_and_fullSupport
    (harmonicBallBoundarySubset_of_volumeGrowth hI2) (regularOpenEqOfAEEq hfull) hfull
  exact annulusMassBoundByHarmonicChainStmt_of_scaledField hI2 h68 h610 h8 hexist hunique hAff hCC

/-- Lemma 11.5 from the Section 5 and 6 inputs, Proposition 8.1, volume
growth, and the cone bad-scales statement. The affine invariance and
coordinate-change hypotheses are staged pending source review. -/
theorem noConeConditionStmt_of_scaledField_and_coneScales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hexist : ExistenceHarmonicBallsStmt.{u})
    (hmany : ManyConeBadScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : NoConeConditionStmt.{u} :=
  noConeConditionStmt_of_comparison_and_coneScales
    (annulusMassBoundByHarmonicChainStmt_of_volumeGrowth hI2 h68 h610 h8 hexist hAff hCC)
    hmany hI2

/-- Proposition 11.2 from the Section 5 and 6 inputs, Proposition 8.1,
volume growth, and the cone bad-scales statement. The affine invariance and
coordinate-change hypotheses are staged pending source review. -/
theorem harmonicBallNotLipschitzStmt_of_scaledField_and_coneScales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hexist : ExistenceHarmonicBallsStmt.{u})
    (hmany : ManyConeBadScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : HarmonicBallNotLipschitzStmt.{u} :=
  harmonicBallNotLipschitzStmt_of_noConeCondition
    (noConeConditionStmt_of_scaledField_and_coneScales hI2 h68 h610 h8 hexist hmany hAff hCC)

end HarmonicBalls
