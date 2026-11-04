import HarmonicBalls.Proofs.Sec6.AnnulusMassCover
import HarmonicBalls.Proofs.Sec6.DiscGreenMass

/-! # Annulus mass and disc Green potentials

The selected-disc mass estimate and the lower bound on the disc Green kernel
combine to give the quantitative potential bound used in Lemma 6.8.
-/

namespace HarmonicBalls.Section6

open Set Metric MeasureTheory
open scoped ENNReal

/-- A disc carrying a prescribed fraction of a set's mass gives a uniform
lower bound on its Green potential. -/
theorem mass_le_disc_green_integral_of_mass_bound {μ : Measure ℂ} {A L : Set ℂ}
    {c : ℂ} {d : ℝ} {N : ℕ} (hd : 0 < d) (hL : MeasurableSet L)
    (hmass : μ (A ∩ L) ≤ (N : ℝ≥0∞) * μ (ball c d ∩ L))
    (hfinite : μ (ball c d ∩ L) ≠ ⊤) (hatom : μ {c} = 0)
    (hint : IntegrableOn (greenFunction (ball c (2 * d)) c) (ball c d ∩ L) μ) :
    ((2 * Real.pi)⁻¹ * Real.log (3 / 2)) * (μ (A ∩ L)).toReal ≤
      (N : ℝ) * ∫ y in ball c d ∩ L, greenFunction (ball c (2 * d)) c y ∂μ := by
  have hmass' := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfinite) hmass
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hmass'
  have hg := inner_disc_mass_le_green_integral hd (measurableSet_ball.inter hL)
    inter_subset_left hfinite hatom hint
  have hk := log_three_halves_green_constant_pos
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

end HarmonicBalls.Section6
