import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.VolumeGrowthAssembly
import HarmonicBalls.Proofs.Sec10.DyadicCrossingAssembly

/-! # Section 9 and 10 statements from volume growth inputs

The affine invariance previously included among the staged assumptions follows
from the covariance characterization of the whole-plane GFF. The remaining
five LQG inputs below are staged in `HarmonicBalls.Proposed.LQG` and await
source review. The typical-scale and subrange prevalence estimates are explicit.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

section

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneLQGBallMassBounds P γ hC hcirc)
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
    LQGMeasureNonatomic P γ α₀ hC hcirc)

include hDG hCC hW hE hN

/-- All-scales volume growth from five staged LQG inputs; affine invariance
is proved from the normalized GFF covariance. -/
theorem lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs :
    LQGVolumeGrowthAllScalesStmt.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_literature hDG
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc)
    hCC hW hE hN

/-- Lemmas 9.3 and 9.4 from the five staged LQG inputs. -/
theorem section9_comparison_lemmas_of_five_staged_inputs :
    HarmonicBallBoundarySubsetStmt.{u} ∧ RegularOpenEqOfAEEqStmt.{u} := by
  have hI2 := lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs hDG hCC hW hE hN
  exact ⟨harmonicBallBoundarySubset_of_volumeGrowth hI2,
    regularOpenEqOfAEEq_of_volumeGrowth hI2⟩

/-- The corrected weak form of Proposition 9.2 from the five staged LQG
inputs and the explicit typical-point good-scale estimate. -/
theorem subharmonicBallUniquenessWeak_of_five_staged_inputs
    (h82 : TypicalPointManyGoodScalesStmt.{u}) : SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales
    (lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs hDG hCC hW hE hN) h82

/-- Lemma 10.1 from the five staged LQG inputs and the explicit subrange
prevalence step. -/
theorem clusterBoundedCrossings_of_five_staged_inputs
    (hsub : VeryGoodAnnuliSubRangeStep.{u}) : ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_volumeGrowth_and_subrange_dyadic
    (lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs hDG hCC hW hE hN) hsub hE hW

end

end HarmonicBalls
