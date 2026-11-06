import HarmonicBalls.Proofs.Sec6.QuantitativeNearbyAnnulus

/-! # Relative collar mass and threshold slack

A relative bound on the concentric boundary collar gives the mass inequality
needed for nearby-centre stability. The bound retains its dependence on the
radius and the displacement; it does not assert a rate for LQG mass.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Metric
open scoped ENNReal

/-- A relative collar-mass bound fits the good-annulus threshold slack if
`a' + (a' + 1) * d ≤ a`. This estimate works at each prescribed radius and
collar width, including when the annulus mass is infinite. -/
theorem annulus_mass_envelope_le_of_relative_collar
    (μ : Measure ℂ) (z : ℂ) {r δ a a' : ℝ} (hδ : 0 < δ) (d : ℝ≥0∞)
    (hcollar : μ (annulus z (3*r-δ) (5*r+δ) \ annulus z (3*r+δ) (5*r-δ)) ≤
      d * μ (annulus z (3*r) (5*r)))
    (hslack : ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal a) :
    ENNReal.ofReal a' * μ (annulus z (3*r-δ) (5*r+δ)) +
      μ (annulus z (3*r-δ) (5*r+δ) \ annulus z (3*r+δ) (5*r-δ)) ≤
      ENNReal.ofReal a * μ (annulus z (3*r) (5*r)) := by
  let A := annulus z (3*r) (5*r)
  let O := annulus z (3*r-δ) (5*r+δ)
  let I := annulus z (3*r+δ) (5*r-δ)
  have hIA : I ⊆ A :=
    (annulus_nearby_center_sandwich (r := 3*r) (R := 5*r)
      (show dist z z < δ by simpa using hδ)).1
  have hO : O ⊆ A ∪ (O \ I) := by
    intro x hx
    by_cases hi : x ∈ I
    · exact Or.inl (hIA hi)
    · exact Or.inr ⟨hx, hi⟩
  have hmass : μ O ≤ μ A + μ (O \ I) :=
    (measure_mono hO).trans (measure_union_le _ _)
  change ENNReal.ofReal a' * μ O + μ (O \ I) ≤ ENNReal.ofReal a * μ A
  calc
    _ ≤ ENNReal.ofReal a' * (μ A + μ (O \ I)) + μ (O \ I) := by gcongr
    _ ≤ ENNReal.ofReal a' * (μ A + d * μ A) + d * μ A := by gcongr
    _ = (ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d) * μ A := by
      simp only [mul_add, add_mul, one_mul]
      simp only [mul_assoc, add_assoc]
    _ ≤ _ := by gcongr

end HarmonicBalls.Section6
