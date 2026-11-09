import HarmonicBalls.Defs.Annuli

/-! # FIRST-PASS helper (fp-S8d, owner n4): two-sided density comparison of measures on a region

For the singular LQG measure `μ` (parameter `α₀ = γ`) and the regular one `lam` (parameter `0`) of the same field,
the Weyl relation off the origin (`LocalLQGInsertionWeylOffOrigin`, FirstPass/Frozen/S8c.lean:59) gives, on a region
`D` avoiding the singularity, `μ|_D = g · lam|_D` with a density `g` bounded between two positive constants. This file
records the measure-level consequence: `μ|_D` is between `c₁ • lam|_D` and `c₂ • lam|_D`. All criteria of the
very-good annulus event are evaluated on sets inside `D` (balls, annuli, Green potentials over `D`), so this
measure-level comparison is all that the criteria comparison needs.

No new mathematics: the statements are the definition of `withDensity` on the restriction and the bounds on the
density. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The restriction of a measure with a density bounded above by `c` on `D` is at most `c • lam|_D`. -/
theorem restrict_le_smul_of_density (lam μ : Measure ℂ) (D : Set ℂ) (hD : MeasurableSet D)
    (g : ℂ → ℝ≥0∞) (c : ℝ≥0∞) (hμ : μ.restrict D = (lam.restrict D).withDensity g)
    (hgc : ∀ y ∈ D, g y ≤ c) : μ.restrict D ≤ c • lam.restrict D := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, hμ, withDensity_apply _ hs, ← setLIntegral_const]
  apply lintegral_mono_ae
  rw [ae_restrict_iff' hs]
  filter_upwards [ae_restrict_mem hD] with y hyD _
  exact hgc y hyD

/-- The restriction of a measure with a density bounded below by `c` on `D` is at least `c • lam|_D`. -/
theorem smul_le_restrict_of_density (lam μ : Measure ℂ) (D : Set ℂ) (hD : MeasurableSet D)
    (g : ℂ → ℝ≥0∞) (c : ℝ≥0∞) (hμ : μ.restrict D = (lam.restrict D).withDensity g)
    (hgc : ∀ y ∈ D, c ≤ g y) : c • lam.restrict D ≤ μ.restrict D := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, hμ, withDensity_apply _ hs, ← setLIntegral_const]
  apply lintegral_mono_ae
  rw [ae_restrict_iff' hs]
  filter_upwards [ae_restrict_mem hD] with y hyD _
  exact hgc y hyD

#print axioms restrict_le_smul_of_density
#print axioms smul_le_restrict_of_density

end HarmonicBalls
