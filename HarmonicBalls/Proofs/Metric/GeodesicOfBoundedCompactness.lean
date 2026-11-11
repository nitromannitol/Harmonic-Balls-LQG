import HarmonicBalls.Steps.Sec11.ProperMetricExtension

/-!
# Geodesics from Euclidean boundedness

A Euclidean length metric has geodesics when its bounded sets are Euclidean
bounded. The proof uses the existing compact-ball geodesic construction and
Heine–Borel compactness on the complex plane.

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open Set

/-- If every closed `D`-ball is Euclidean bounded, then it is compact in the
Euclidean topology. -/
theorem IsEuclideanLengthMetric.isCompact_closedBall_of_isBounded
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hbounded : ∀ x : ℂ, ∀ R : ℝ,
      Bornology.IsBounded {z : ℂ | D x z ≤ R})
    (x : ℂ) (R : ℝ) : IsCompact {z : ℂ | D x z ≤ R} := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨?_, hbounded x R⟩
  have hc : Continuous fun z : ℂ => D x z := by
    simpa only [hD.symm x] using hD.continuous_left x
  exact isClosed_le hc continuous_const

/-- A Euclidean length metric whose closed balls are Euclidean bounded admits
a constant-speed geodesic between any two points. -/
theorem IsEuclideanLengthMetric.exists_geodesic_of_isBounded_closedBalls
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hbounded : ∀ x : ℂ, ∀ R : ℝ,
      Bornology.IsBounded {z : ℂ | D x z ≤ R})
    (x y : ℂ) : ∃ p : Path x y, ∀ s t : Icc (0 : ℝ) 1,
      D (p s) (p t) = |(s : ℝ) - (t : ℝ)| * D x y := by
  have hnonneg : ∀ x y, 0 ≤ D x y := by
    intro x y
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  exact hD.exists_geodesic_of_compact_closedBalls hnonneg
    (hD.isCompact_closedBall_of_isBounded hbounded) x y

/-- A Euclidean length metric admits constant-speed geodesics if each set
bounded in that metric is Euclidean bounded. -/
theorem IsEuclideanLengthMetric.exists_geodesic_of_bounded_sets
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hbounded : ∀ S : Set ℂ,
      (∃ x : ℂ, ∃ R : ℝ, ∀ z ∈ S, D x z ≤ R) → Bornology.IsBounded S)
    (x y : ℂ) : ∃ p : Path x y, ∀ s t : Icc (0 : ℝ) 1,
      D (p s) (p t) = |(s : ℝ) - (t : ℝ)| * D x y := by
  apply hD.exists_geodesic_of_isBounded_closedBalls ?_ x y
  intro z R
  exact hbounded _ ⟨z, R, fun _ hw => hw⟩


end HarmonicBalls
