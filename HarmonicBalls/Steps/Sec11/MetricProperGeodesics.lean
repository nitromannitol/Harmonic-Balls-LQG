import HarmonicBalls.Steps.Sec11.ProperMetricExtension
import HarmonicBalls.Steps.Sec11.MetricField
import HarmonicBalls.Proposed.MetricProperness

/-!
# Geodesics for proper LQG metrics

The whole-plane conclusion uses the staged whole-plane bounded-compactness
input. For the logarithmically singular field, bounded compactness remains a
separate explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set

/-- Under bounded compactness and the staged metric-field input, the metric
of the logarithmically singular field has geodesics almost surely. -/
theorem ae_exists_geodesic_of_metricFieldAxioms_of_compact_closedBalls
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hcompact : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D ω x z ≤ R}) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ, ∃ p : Path x y, ∀ s t : Icc (0 : ℝ) 1,
      D ω (p s) (p t) = |(s : ℝ) - (t : ℝ)| * D ω x y := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD, hcompact] with ω hlength hcompact
  have hnonneg : ∀ x y, 0 ≤ D ω x y := by
    intro x y
    have h := hlength.triangle x y x
    rw [hlength.self_eq_zero, hlength.symm y x] at h
    linarith
  intro x y
  exact hlength.exists_geodesic_of_compact_closedBalls hnonneg hcompact x y

/-- The staged whole-plane bounded-compactness input and the LQG metric axioms
imply existence of geodesics for the whole-plane metric almost surely. -/
theorem ae_exists_geodesic_wholePlane_of_boundedlyCompact
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (hproper : WholePlaneLQGMetricBoundedlyCompact P γ ξ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ, ∃ p : Path x y, ∀ s t : Icc (0 : ℝ) 1,
      𝔇 (hC ω) (p s) (p t) = |(s : ℝ) - (t : ℝ)| * 𝔇 (hC ω) x y := by
  have heq : ∀ ω, addFunPairing (hC ω) (fun _ => 0) = hC ω := by
    intro ω
    funext φ
    simp [addFunPairing]
  have hlength := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) hgff
    (by intro ω; fun_prop) (by intro x; fun_prop)).ae_isEuclideanLengthMetric
  simp only [heq] at hlength
  filter_upwards [hlength, hproper hgff hγ hγ₂ 𝔇 h𝔇] with ω hlength hcompact
  have hnonneg : ∀ x y, 0 ≤ 𝔇 (hC ω) x y := by
    intro x y
    have h := hlength.triangle x y x
    rw [hlength.self_eq_zero, hlength.symm y x] at h
    linarith
  intro x y
  exact hlength.exists_geodesic_of_compact_closedBalls hnonneg hcompact x y

end HarmonicBalls
