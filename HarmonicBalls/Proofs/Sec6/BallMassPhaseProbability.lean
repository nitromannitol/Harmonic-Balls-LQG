import HarmonicBalls.Proofs.Sec6.BallMassPhaseBounds
import HarmonicBalls.Proofs.Sec6.BallMassSizeWindow
import HarmonicBalls.Proofs.Sec6.UniformProbabilityWindows

/-! # Ball-mass windows over compact dyadic phases -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- All-scales volume growth gives a ball-mass size window with a failure
probability uniform over all phases in `[1/2,1]`. -/
theorem exists_ballMassSize_window_on_dyadic_phases
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {γ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hβ : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - 0)) < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ ∀ s ∈ Icc (1 / 2 : ℝ) 1,
      P {ω | annulusBallMassSize (μ ω) β s 0 /
        (μ ω) (annulus 0 (s / 4) (2 * s)) ∉
          Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ := by
  let F : Ω → ℝ → ℝ≥0∞ := fun ω s => annulusBallMassSize (μ ω) β s 0 /
    (μ ω) (annulus 0 (s / 4) (2 * s))
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨hβp, hβp', _⟩ := volumeGrowthExponents_mem hγ hγ₂ hQ
  have hV := ae_isLocallyFiniteMeasure_volumeGrowth_of_exponents hgrowth hγ hγ₂ hQ
    hβp hβp' hβ hgff hμ
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ₂ hQ
    Ω P hC hcirc μ hgff hμ
  apply exists_uniform_ennreal_window_of_ae_bounds P (Icc (1 / 2 : ℝ) 1) F
  · intro s hs
    exact (measurable_annulusBallMassSize_ratio β s 0 (by linarith [hs.1])).comp_aemeasurable
      (hgff.aemeasurable_lqgMeasure hμ)
  · filter_upwards [hV, hfull] with ω hω hf
    let : IsLocallyFiniteMeasure (μ ω) := hω.1
    let A : Set ℂ := annulus 0 (1 / 4) 1
    have hA : 0 < (μ ω) A := by
      apply hf A (isOpen_ball.sdiff isClosed_closedBall)
      refine ⟨(1 / 2 : ℂ), ?_⟩
      change dist (1 / 2 : ℂ) 0 < 1 ∧ ¬ dist (1 / 2 : ℂ) 0 ≤ 1 / 4
      norm_num [dist_eq_norm, Complex.norm_def]
    have hB : (μ ω) (ball 0 2) ≠ ∞ :=
      (measure_ball_lt_top (μ := μ ω) (x := (0 : ℂ)) (r := 2)).ne
    obtain ⟨c, hc, hcM⟩ := exists_ballMassSize_lower_bound_on_dyadic_phases (hω.2 2 (by norm_num))
    let d : ℝ≥0∞ := ENNReal.ofReal ((1 / 8 : ℝ) ^ β)
    have hd : d ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) β)).ne'
    refine ⟨ENNReal.ofReal c / (μ ω) (ball 0 2),
      ((μ ω) (ball 0 2) / d) / (μ ω) A,
      ENNReal.div_pos (ENNReal.ofReal_pos.mpr hc).ne' hB,
      ENNReal.div_ne_top (ENNReal.div_ne_top hB hd) hA.ne', ?_⟩
    intro s hs
    have hsub : A ⊆ annulus 0 (s / 4) (2 * s) := by
      intro x hx
      exact ⟨ball_subset_ball (by linarith [hs.1]) hx.1,
        fun h => hx.2 (closedBall_subset_closedBall (by linarith [hs.2]) h)⟩
    have hbig : annulus 0 (s / 4) (2 * s) ⊆ ball (0 : ℂ) 2 :=
      fun _ hx => ball_subset_ball (by linarith [hs.2]) hx.1
    constructor
    · exact ENNReal.div_le_div (hcM s hs) (measure_mono hbig)
    · exact ENNReal.div_le_div (ballMassSize_upper_bound_on_dyadic_phases (μ ω) β hs)
        (measure_mono hsub)
  · exact hδ

end HarmonicBalls.Section6
