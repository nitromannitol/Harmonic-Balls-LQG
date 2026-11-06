import HarmonicBalls.Proofs.Sec11.AnnulusMassComparison
import HarmonicBalls.Proofs.Sec6.AnnulusMassAssembly
import HarmonicBalls.Proofs.Sec6.AnnulusOdometerAssembly
import HarmonicBalls.Proofs.Sec2.Assembly
import HarmonicBalls.Proofs.Sec5.ExistenceFromVolumeGrowth
import HarmonicBalls.Proofs.Sec5.NoEntryPropagation
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.RegularOpenEqOfAEEq

/-!
# Lemma 11.6 from the staged LQG inputs

`AnnulusMassBoundByHarmonicChainStmt` (Lemma 11.6, lemma:harmonic-comparison-chain) is assembled here from the
radius-general Lemmas 6.8 and 6.10 (`AnnulusMassBoundByOdometerStmt`, `OdometerBoundByAnnulusMassStmt`, through their
literature wrappers), the volume growth I2, the full support I1, the Section 5 existence and uniqueness of harmonic
balls, and the scaled-field comparison `annulusMassBoundByHarmonicChainStmt_of_scaledField`.

Explicit hypotheses of the main theorem:
* the staged LQG inputs of `HarmonicBalls.Proposed.LQG` (`WholePlaneLQGBallMassBounds`,
  `WholePlaneGFFAffineInvariance`, `LQGMeasureCoordChange`, `LQGMeasureWeylScaling`, `LQGMeasureExistence`,
  `LQGMeasureNonatomic`), pending operator source check;
* `BoundaryMeasureZeroOfCompactClusterStmt` (Proposition 8.1) and `HarnackTypeEstimateStmt` (Section 6).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Section6

universe u

/-- Lemma 11.6 with the staged LQG inputs and the two section statements `h8` (Proposition 8.1) and `h61`
(the Section 6 Harnack estimate) as explicit hypotheses. Every other input is derived from the staged inputs
through the proved literature wrappers. -/
theorem annulusMassBoundByHarmonicChainStmt_of_stagedInputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) :
    AnnulusMassBoundByHarmonicChainStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  have hI2 : LQGVolumeGrowthAllScalesStmt.{u} :=
    lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC0 hW hE hN
  have hvolume : LiouvilleVolumeGrowthStmt.{u} :=
    liouvilleVolumeGrowthStmt_of_literature hDG hAff hCC0 hW hE hN
  have hfull : LQGMeasureFullSupportStmt.{u} :=
    lqgMeasureFullSupportStmt_of_literature hDG hAff hCC0 hW hE hN
  have h68 : AnnulusMassBoundByOdometerStmt.{u} :=
    annulusMassBoundByOdometer_of_literature hDG hAff hCC0 hW hE hN
  have h610 : OdometerBoundByAnnulusMassStmt.{u} :=
    odometerBoundByAnnulusMass_of_volumeGrowth hI2
  have hexist : ExistenceHarmonicBallsStmt.{u} :=
    existenceHarmonicBalls_of_harnack_and_compactBoundary hI2 hvolume h61 h8
      (fun P hC hcirc => hAff _ P hC hcirc) (fun P γ α₀ hC hcirc => hCC _ P γ α₀ hC hcirc)
  have h93 : HarmonicBallBoundarySubsetStmt.{u} :=
    harmonicBallBoundarySubset_of_literature hDG hAff hCC0 hW hE hN
  have hunique : UniquenessHarmonicBallsStmt.{u} :=
    uniquenessHarmonicBalls_of_boundary_and_fullSupport h93 (regularOpenEqOfAEEq hfull) hfull
  exact annulusMassBoundByHarmonicChainStmt_of_scaledField hI2 h68 h610 h8 hexist hunique hAff hCC

end HarmonicBalls

#print axioms HarmonicBalls.annulusMassBoundByHarmonicChainStmt_of_stagedInputs
