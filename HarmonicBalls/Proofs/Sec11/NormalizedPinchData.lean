import HarmonicBalls.Proofs.Sec11.ShiftedNormalizedMeasureDecoder
import HarmonicBalls.Proofs.Sec8.VeryGoodLocality
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable

/-! # Pinching data from a normalized local measure

Masses and annular Green-potential suprema are measurable functions of the
normalized local measure. The identities below retain the normalization
factor even when it is zero or infinite.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- The normalized restriction determines every contained measurable mass and
annular Green-potential supremum, with their common normalizing factor. -/
theorem normalizedRestriction_mass_green (μ : Measure ℂ) (U A : Set ℂ)
    (hA : MeasurableSet A) (hAU : A ⊆ U) (z : ℂ) (a b : ℝ)
    (hann : annulus z a b ⊆ U) :
    normalizedRestriction μ U A = (μ U)⁻¹ * μ A ∧
      annulusGreenPotentialSup (normalizedRestriction μ U) z a b =
        (μ U)⁻¹ * annulusGreenPotentialSup μ z a b := by
  constructor
  · rw [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hA, inter_eq_left.mpr hAU]
  · rw [normalizedRestriction, annulusGreenPotentialSup_smul,
      annulusGreenPotentialSup_restrict μ z a b U hann]

/-- A mass, an annular Green-potential supremum and a countable collection of
metric observables are jointly measurable in the normalized measure and the
metric observables. -/
theorem measurable_mass_green_metric (A : Set ℂ) (hA : MeasurableSet A)
    (z : ℂ) (a b : ℝ) :
    Measurable (fun p : Measure ℂ × (ℕ → ℝ≥0∞) =>
      ((p.1 A, annulusGreenPotentialSup p.1 z a b), p.2)) := by
  exact (((Measure.measurable_coe hA).comp measurable_fst).prodMk
    ((measurable_annulusGreenPotentialSup z a b).comp measurable_fst)).prodMk measurable_snd

#print axioms normalizedRestriction_mass_green
#print axioms measurable_mass_green_metric

end HarmonicBalls
