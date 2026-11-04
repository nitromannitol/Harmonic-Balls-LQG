import HarmonicBalls.Proofs.Sec6.PositiveRandomWindow
import HarmonicBalls.Proofs.Sec8.GreenKernelContinuity
import HarmonicBalls.Steps.Sec11.PinchGreenFinite
import HarmonicBalls.Proofs.Sec11.ConeGreenPositive
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-! # Green-potential size windows for LQG annuli -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Volume growth supplies a positive finite Green-potential ratio on every
fixed centred annulus at positive scale. -/
theorem ae_greenSizeRatio_pos_ne_top_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, 0 < annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
        (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∧
      annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
        (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ≠ ∞ := by
  have hne : (annulus (0 : ℂ) (ρ / 4) (2 * ρ)).Nonempty := by
    refine ⟨(ρ : ℂ), ?_⟩
    change dist (ρ : ℂ) 0 < 2 * ρ ∧ ¬ dist (ρ : ℂ) 0 ≤ ρ / 4
    have hd : dist (ρ : ℂ) 0 = ρ := by simp [dist_eq_norm, hρ.le]
    rw [hd]
    constructor <;> linarith
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ₂ hα hgff hμ
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α₀ hγ hγ₂ hα
    Ω P hC hcirc μ hgff hμ
  filter_upwards [hV, hfull,
    ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth hgrowth hγ hγ₂ hα hgff hμ
      (ρ / 4) (show 0 < 2 * ρ by positivity)] with ω hω hf htop
  let : IsLocallyFiniteMeasure (μ ω) := hω.1
  have hopen : IsOpen (annulus (0 : ℂ) (ρ / 4) (2 * ρ)) :=
    isOpen_ball.sdiff isClosed_closedBall
  have hmasspos := hf _ hopen hne
  have hmasstop : (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (measure_ball_lt_top (μ := μ ω) (x := (0 : ℂ)) (r := 2 * ρ)).ne
    exact measure_mono (fun _ hx => hx.1)
  have hgreen := annulusGreenPotentialSup_pos_of_fullSupport (μ ω) 0 (ρ / 4) (2 * ρ) hf hne
  exact ⟨ENNReal.div_pos hgreen.ne' hmasstop, ENNReal.div_ne_top htop hmasspos.ne'⟩

/-- The Green-potential size criterion has an arbitrarily high-probability
positive deterministic window, conditional on all-scales volume growth. -/
theorem exists_greenSize_window_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₂m C₂p : ℝ, 0 < C₂m ∧ 0 < C₂p ∧
      P {ω | annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
        (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∉
          Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  exact exists_ennreal_window_of_ae_pos_ne_top P
    ((measurable_annulusGreenPotentialRatio_zero ρ).comp_aemeasurable
      (hgff.aemeasurable_lqgMeasure hμ))
    (ae_greenSizeRatio_pos_ne_top_of_volumeGrowth hgrowth hγ hγ₂ hα hgff hμ hρ) hδ

end HarmonicBalls.Section6
