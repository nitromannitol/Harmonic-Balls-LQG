import HarmonicBalls.Proofs.Sec6.PositiveRandomWindow
import HarmonicBalls.Proofs.Sec8.BallMassCountable
import HarmonicBalls.Proofs.Sec8.GreenKernelContinuity

/-! # High-probability size windows for very-good annuli -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter
open scoped ENNReal

/-- At a fixed centred annulus, almost-sure positivity and finiteness of the
ball-mass and Green-potential ratios give deterministic positive windows for
both size criteria, each with an arbitrarily small failure probability. -/
theorem exists_veryGood_size_windows_of_ae_positive_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P) (β ρ : ℝ) (hρ : 0 < ρ)
    (hsize : ∀ᵐ ω ∂P,
      (0 < annulusBallMassSize (μ ω) β ρ 0 / (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∧
        annulusBallMassSize (μ ω) β ρ 0 / (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ≠ ∞) ∧
      (0 < annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
          (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∧
        annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
          (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ≠ ∞))
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      P {ω | annulusBallMassSize (μ ω) β ρ 0 / (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
        (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  obtain ⟨C₁m, C₁p, h1m, h1p, h1⟩ := exists_ennreal_window_of_ae_pos_ne_top P
    ((measurable_annulusBallMassSize_ratio β ρ 0 hρ).comp_aemeasurable hμ)
    (hsize.mono fun _ h => h.1) hδ
  obtain ⟨C₂m, C₂p, h2m, h2p, h2⟩ := exists_ennreal_window_of_ae_pos_ne_top P
    ((measurable_annulusGreenPotentialRatio_zero ρ).comp_aemeasurable hμ)
    (hsize.mono fun _ h => h.2) hδ
  exact ⟨C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, h1, h2⟩

end HarmonicBalls.Section6
