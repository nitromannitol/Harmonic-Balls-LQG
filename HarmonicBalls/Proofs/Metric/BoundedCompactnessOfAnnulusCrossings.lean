import HarmonicBalls.Proofs.Metric.PropernessOfAnnulusCrossings
import HarmonicBalls.Proofs.Metric.GeodesicOfBoundedCompactness

/-!
# Compactness and geodesics from annulus crossings

Divergent deterministic lower bounds for ordered radial annulus crossings imply
bounded compactness and constant-speed geodesics. We acknowledge Leonardo
Bonanno's contributions to this formalization, including the pinned
Lattice-Probability `lean-v4.35` development.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- A closed set bounded in `D` is compact when ordered radial annuli have
divergent sums of lower crossing-length bounds. Closedness and compactness are
in the Euclidean topology, which `D` induces. -/
theorem IsEuclideanLengthMetric.isCompact_of_radialCrossing_lowerBounds
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (center : ℂ) (r R : ℕ → ℝ) (a : ℕ → ℝ≥0∞)
    (hr : ∀ i, 0 ≤ r i) (hband : ∀ i, r i ≤ R i)
    (hordered : ∀ i j, i < j → R i ≤ r j)
    (ha : ∀ i, a i ≤ radialAnnulusCrossingLength D center (r i) (R i))
    (hdiv : ∀ C : ℝ, ∃ n : ℕ, ENNReal.ofReal C < ∑ i ∈ Finset.range n, a i)
    (S : Set ℂ) (hclosed : IsClosed S)
    (hS : ∃ x C, ∀ z ∈ S, D x z ≤ C) : IsCompact S := by
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hclosed, hD.isBounded_of_radialCrossing_lowerBounds
      center r R a hr hband hordered ha hdiv S hS⟩

/-- Divergent lower bounds for ordered radial annulus crossings imply that
any two points can be joined by a constant-speed `D`-geodesic. -/
theorem IsEuclideanLengthMetric.exists_geodesic_of_radialCrossing_lowerBounds
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (center : ℂ) (r R : ℕ → ℝ) (a : ℕ → ℝ≥0∞)
    (hr : ∀ i, 0 ≤ r i) (hband : ∀ i, r i ≤ R i)
    (hordered : ∀ i j, i < j → R i ≤ r j)
    (ha : ∀ i, a i ≤ radialAnnulusCrossingLength D center (r i) (R i))
    (hdiv : ∀ C : ℝ, ∃ n : ℕ, ENNReal.ofReal C < ∑ i ∈ Finset.range n, a i)
    (x y : ℂ) : ∃ p : Path x y, ∀ s t : Icc (0 : ℝ) 1,
      D (p s) (p t) = |(s : ℝ) - (t : ℝ)| * D x y := by
  exact hD.exists_geodesic_of_bounded_sets
    (hD.isBounded_of_radialCrossing_lowerBounds center r R a hr hband hordered ha hdiv) x y


end HarmonicBalls
