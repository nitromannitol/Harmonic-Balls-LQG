import HarmonicBalls.Proofs.Sec9.StrongMinimum
import HarmonicBalls.Steps.Sec4.Basic
import HarmonicBalls.Steps.Sec2.VolumeGrowth
import HarmonicBalls.Proofs.Sec2.Assembly

/-!
# Lemma 9.3 from LQG volume growth

The deterministic boundary comparison is applied on an almost sure event with volume growth
and full support. The ambient disc is enlarged to contain both ball closures.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Lemma 9.3, given the all-scales volume-growth estimate I2. -/
theorem harmonicBallBoundarySubset_of_volumeGrowth (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    HarmonicBallBoundarySubsetStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ Λhat hfamily
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hI1 := lqgMeasureFullSupportStmt_of_volumeGrowth hI2
  filter_upwards [hV, hI1 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hfamily] with ω hω hsupport hfam
  let : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hsupport U hU hne).ne'⟩
  intro A z R t hz hAcl hA ht hmass
  have hR : 0 < R := pos_of_mem_ball hz
  obtain ⟨r, hr⟩ := (((hfam z).1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let S := max R r + 1
  have hS : 0 < S := by
    have := le_max_left R r
    dsimp [S]
    linarith
  have hRS : R ≤ S := by
    have := le_max_left R r
    dsimp [S]
    linarith
  have hrS : r ≤ S := by
    have := le_max_right R r
    dsimp [S]
    linarith
  have hBmass : (μ ω).real A = (μ ω).real (Λhat ω z t) := by
    rw [measureReal_def, measureReal_def, hmass, (hfam z).1.measure_eq t ht]
  exact hA.frontier_subset_closure_of_volumeGrowth hω.1 ((hfam z).2.1 t ht) hS (hω.2 S hS)
    (hAcl.trans (ball_subset_ball hRS)) (hr.trans (ball_subset_ball hrS)) hBmass

/-- Lemma 9.3 from the six literature inputs staged in `HarmonicBalls.Proposed.LQG`,
pending source review. -/
theorem harmonicBallBoundarySubset_of_literature
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    HarmonicBallBoundarySubsetStmt.{u} :=
  harmonicBallBoundarySubset_of_volumeGrowth (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN)

end HarmonicBalls
