import HarmonicBalls.Steps.Sec11.PinchDiameterFiniteness

/-!
# Internal distances on connected open sets

A Euclidean length metric has finite internal distance on a connected open
set, uniformly over compact subsets. The local comparison and compactness
arguments are supplied by the existing internal-metric API.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- Nonnegativity follows from symmetry, the triangle inequality, and zero
self-distance in the definition of a Euclidean length metric. -/
theorem IsEuclideanLengthMetric.distance_nonneg
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) :
    0 ≤ D x y := by
  have h := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at h
  linarith

/-- Locally, the internal distance agrees with the ambient length metric. -/
theorem IsEuclideanLengthMetric.internalDistance_eq_near
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y, D x y < δ →
      internalMetric D U x y = ENNReal.ofReal (D x y) :=
  hD.internalMetric_eq_of_near hD.distance_nonneg hU hx

/-- The internal distance between two points of a connected open set is finite. -/
theorem IsEuclideanLengthMetric.internalDistance_lt_top_of_connected_open
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    internalMetric D U x y < ∞ :=
  hD.internalMetric_lt_top_of_joinedIn hD.distance_nonneg hU
    ((hU.isConnected_iff_isPathConnected.mp hconn).joinedIn x hx y hy)

/-- A compact subset of a connected open set has finite internal diameter. -/
theorem IsEuclideanLengthMetric.internalDistance_compact_uniform_lt_top
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U K : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (⨆ x ∈ K, ⨆ y ∈ K, internalMetric D U x y) < ∞ :=
  hD.iSup_pair_internalMetric_lt_top_of_isCompact hD.distance_nonneg hU hconn hK hKU

#print axioms IsEuclideanLengthMetric.distance_nonneg
#print axioms IsEuclideanLengthMetric.internalDistance_eq_near
#print axioms IsEuclideanLengthMetric.internalDistance_lt_top_of_connected_open
#print axioms IsEuclideanLengthMetric.internalDistance_compact_uniform_lt_top

end HarmonicBalls
