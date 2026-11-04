import HarmonicBalls.Proofs.Sec10.DyadicCrossingAssembly
import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence
import HarmonicBalls.Proofs.Sec9.ExistenceResultsAssembly

/-! # Annular crossings from volume growth and LQG existence

The prevalence estimate follows from the Section 6 fine-support argument.
The LQG existence and other literature assumptions below are staged and
await source review; the Section 6 dependency chain also awaits audit.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Lemma 10.1 follows from volume growth and zero-strength LQG existence. -/
theorem clusterBoundedCrossings_of_volumeGrowth_and_zero_existence
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_volumeGrowth_and_prevalence_dyadic hI2
    (Section6.manyVeryGoodAnnuliStmt_of_volumeGrowth_zero_existence hI2 hE0)

/-- Lemma 10.1 follows from the staged whole-plane mass bound, coordinate
change, and existence at all subcritical singularity strengths. -/
theorem clusterBoundedCrossings_of_three_staged_inputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc) : ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_volumeGrowth_and_zero_existence
    (lqgVolumeGrowthAllScalesStmt_of_existence hDG hCC hE)
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)

end HarmonicBalls
