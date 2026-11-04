import HarmonicBalls.Proofs.Sec9.NumberedResultsAssembly
import HarmonicBalls.Proofs.Sec6.SingularityOriginNonatomic

/-! # Section 9 and 10 results from LQG existence

The non-atomicity and Weyl-scaling inputs in the earlier assembly follow
from the multiscale mass estimate and existence at every subcritical
singularity. The three remaining literature inputs are staged and await
source review; the good-scale and subrange estimates remain explicit.
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
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureExistence P γ α hC hcirc)

include hDG hCC hE

/-- All-scales volume growth from the staged mass bound, coordinate change,
and existence at all singularity strengths. Non-atomicity is derived using
existence at a strictly stronger subcritical singularity. -/
theorem lqgVolumeGrowthAllScalesStmt_of_existence :
    LQGVolumeGrowthAllScalesStmt.{u} := by
  have hS : WholePlaneScaledBallMassStep.{u} :=
    wholePlaneScaledBallMassStep_of_rescaled
      (rescaledBallMassUniformStep_of_DG hDG
        (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc)
        hCC wholePlaneGFFMixtureStep_holds)
  apply lqgVolumeGrowthAllScalesStmt_of_five_staged_inputs hDG hCC
    (fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
  intro Ω _ P γ α hC hcirc
  exact Section6.lqgMeasureNonatomic_of_existence hS P γ α hC hcirc
    (fun β => hE Ω P γ β hC hcirc)

/-- Lemmas 9.3 and 9.4 under the three staged inputs. -/
theorem section9_comparison_lemmas_of_existence :
    HarmonicBallBoundarySubsetStmt.{u} ∧ RegularOpenEqOfAEEqStmt.{u} := by
  have hI2 := lqgVolumeGrowthAllScalesStmt_of_existence hDG hCC hE
  exact ⟨harmonicBallBoundarySubset_of_volumeGrowth hI2,
    regularOpenEqOfAEEq_of_volumeGrowth hI2⟩

/-- Corrected weak Proposition 9.2 also requires the explicit typical-point
good-scale estimate. -/
theorem subharmonicBallUniquenessWeak_of_existence
    (h82 : TypicalPointManyGoodScalesStmt.{u}) : SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales
    (lqgVolumeGrowthAllScalesStmt_of_existence hDG hCC hE) h82

/-- Lemma 10.1 also requires the explicit subrange prevalence estimate. -/
theorem clusterBoundedCrossings_of_existence
    (hsub : VeryGoodAnnuliSubRangeStep.{u}) : ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_volumeGrowth_and_subrange_dyadic
    (lqgVolumeGrowthAllScalesStmt_of_existence hDG hCC hE) hsub
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
    (fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)

end

end HarmonicBalls
