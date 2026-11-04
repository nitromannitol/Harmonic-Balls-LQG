import HarmonicBalls.Proofs.Sec6.BallMassSizePositive
import HarmonicBalls.Proofs.Sec6.GreenSizeWindow
import HarmonicBalls.Proofs.Sec6.VeryGoodSizeWindows
import HarmonicBalls.Steps.Sec4.Basic

/-! # Ball-mass size windows for LQG annuli -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- All-scales volume growth gives a positive finite ball-mass ratio for any
exponent in its lower-growth range. -/
theorem ae_ballMassSizeRatio_pos_ne_top_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hβ : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, 0 < annulusBallMassSize (μ ω) β ρ 0 /
        (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∧
      annulusBallMassSize (μ ω) β ρ 0 /
        (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ≠ ∞ := by
  have hne : (annulus (0 : ℂ) (ρ / 4) (2 * ρ)).Nonempty := by
    refine ⟨(ρ : ℂ), ?_⟩
    change dist (ρ : ℂ) 0 < 2 * ρ ∧ ¬ dist (ρ : ℂ) 0 ≤ ρ / 4
    have hd : dist (ρ : ℂ) 0 = ρ := by simp [dist_eq_norm, hρ.le]
    rw [hd]
    constructor <;> linarith
  obtain ⟨hβp, hβp', _⟩ := volumeGrowthExponents_mem hγ hγ₂ hα
  have hV := ae_isLocallyFiniteMeasure_volumeGrowth_of_exponents hgrowth hγ hγ₂ hα
    hβp hβp' hβ hgff hμ
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α₀ hγ hγ₂ hα
    Ω P hC hcirc μ hgff hμ
  filter_upwards [hV, hfull] with ω hω hf
  let : IsLocallyFiniteMeasure (μ ω) := hω.1
  have hopen : IsOpen (annulus (0 : ℂ) (ρ / 4) (2 * ρ)) :=
    isOpen_ball.sdiff isClosed_closedBall
  have hmasspos := hf _ hopen hne
  have hmasstop : (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (measure_ball_lt_top (μ := μ ω) (x := (0 : ℂ)) (r := 2 * ρ)).ne
    exact measure_mono (fun _ hx => hx.1)
  have hpos := annulusBallMassSize_pos_of_volumeGrowth hρ (hω.2 (2 * ρ) (by positivity))
  have htop := annulusBallMassSize_ne_top_of_locallyFinite (μ ω) hρ β
  exact ⟨ENNReal.div_pos hpos.ne' hmasstop, ENNReal.div_ne_top htop hmasspos.ne'⟩

/-- At a fixed centred annulus, both size criteria have deterministic positive
windows with arbitrarily small failure probabilities, under volume growth. -/
theorem exists_veryGood_size_windows_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {γ α₀ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hβ : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      P {ω | annulusBallMassSize (μ ω) β ρ 0 / (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
        (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  apply exists_veryGood_size_windows_of_ae_positive_finite P (hgff.aemeasurable_lqgMeasure hμ) β ρ hρ
  · filter_upwards [ae_ballMassSizeRatio_pos_ne_top_of_volumeGrowth hgrowth hγ hγ₂ hα hβ hgff hμ hρ,
      ae_greenSizeRatio_pos_ne_top_of_volumeGrowth hgrowth hγ hγ₂ hα hgff hμ hρ] with ω h₁ h₂
    exact ⟨h₁, h₂⟩
  · exact hδ

end HarmonicBalls.Section6
