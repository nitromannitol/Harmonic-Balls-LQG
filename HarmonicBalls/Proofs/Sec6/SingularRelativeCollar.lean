import HarmonicBalls.Proofs.Sec6.QuantitativeCollarMass
import HarmonicBalls.Proofs.Sec6.SizeRatioSingularWeight

/-! # Relative mass bounds under singular Weyl weights

Relative mass estimates transfer in both directions on a separated size
annulus, with the distortion retaining its dependence on the exponent.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- Comparable measures transfer a relative mass bound in both directions.
The sets need only lie in the region of comparison. -/
theorem relative_mass_bounds_of_comparableWith
    {μ ν : Measure ℂ} {B A C : Set ℂ} {c K d : ℝ≥0∞}
    (h : IsComparableOnWith μ ν B c K) (hA : A ⊆ B) (hC : C ⊆ B) :
    (ν C ≤ d * ν A → μ C ≤ (K * d) * μ A) ∧
    (μ C ≤ d * μ A → ν C ≤ (K * d) * ν A) := by
  constructor
  · intro hd
    calc
      μ C ≤ K * c * ν C := h.apply_le hC
      _ ≤ K * c * (d * ν A) := by gcongr
      _ = (K * d) * (c * ν A) := by ac_rfl
      _ ≤ (K * d) * μ A := by gcongr; exact h.le_apply hA
  · intro hd
    apply (ENNReal.mul_le_mul_iff_right h.scale_ne_zero h.scale_ne_top).1
    calc
      c * ν C ≤ μ C := h.le_apply hC
      _ ≤ d * μ A := hd
      _ ≤ d * (K * c * ν A) := by gcongr; exact h.apply_le hA
      _ = c * ((K * d) * ν A) := by ac_rfl

/-- A singular power weight transfers relative mass estimates on a separated
size annulus. The constant is independent of the radius and centre but depends
on the exponent. -/
theorem relative_mass_bounds_of_singular_weight
    {μ ν : Measure ℂ} {ρ e : ℝ} {x₀ : ℂ} {A C : Set ℂ} {d : ℝ≥0∞}
    (hρ : 0 < ρ) (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)))
    (hμ : μ.restrict {0}ᶜ =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hA : A ⊆ annulus x₀ (ρ / 4) (2 * ρ))
    (hC : C ⊆ annulus x₀ (ρ / 4) (2 * ρ)) :
    (ν C ≤ d * ν A → μ C ≤ (ENNReal.ofReal (((401 : ℝ) ^ |e|) ^ 2) * d) * μ A) ∧
    (μ C ≤ d * μ A → ν C ≤ (ENNReal.ofReal (((401 : ℝ) ^ |e|) ^ 2) * d) * ν A) := by
  obtain ⟨c, hc⟩ := isComparableOnWith_size_annulus_of_weight hρ hd hμ
  exact relative_mass_bounds_of_comparableWith hc hA hC

/-- A collar estimate for a singular measure supplies the zero-singularity
mass envelope at the same prescribed radius and displacement. Both the
annulus and its enlarged collar must lie in the separated size annulus. -/
theorem zero_mass_envelope_of_singular_collar
    {μ ν : Measure ℂ} {ρ e r δ a a' : ℝ} {x₀ z : ℂ} {d : ℝ≥0∞}
    (hρ : 0 < ρ) (hδ : 0 < δ)
    (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)))
    (hμ : μ.restrict {0}ᶜ =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hA : annulus z (3*r) (5*r) ⊆ annulus x₀ (ρ / 4) (2 * ρ))
    (hO : annulus z (3*r-δ) (5*r+δ) ⊆ annulus x₀ (ρ / 4) (2 * ρ))
    (hcollar : μ (annulus z (3*r-δ) (5*r+δ) \ annulus z (3*r+δ) (5*r-δ)) ≤
      d * μ (annulus z (3*r) (5*r)))
    (hslack : ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) *
      (ENNReal.ofReal (((401 : ℝ) ^ |e|) ^ 2) * d) ≤ ENNReal.ofReal a) :
    ENNReal.ofReal a' * ν (annulus z (3*r-δ) (5*r+δ)) +
      ν (annulus z (3*r-δ) (5*r+δ) \ annulus z (3*r+δ) (5*r-δ)) ≤
      ENNReal.ofReal a * ν (annulus z (3*r) (5*r)) := by
  apply annulus_mass_envelope_le_of_relative_collar ν z hδ _ _ hslack
  exact (relative_mass_bounds_of_singular_weight hρ hd hμ hA
    (sdiff_subset.trans hO)).2 hcollar

end HarmonicBalls.Section6
