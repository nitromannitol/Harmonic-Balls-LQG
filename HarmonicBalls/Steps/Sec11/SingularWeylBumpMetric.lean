import HarmonicBalls.Steps.Sec11.WeylPathConcatenation
import HarmonicBalls.Steps.Sec11.SingularWeylBumpSymmetry

/-! # Metric properties of a singular-field Weyl bump

The metric-field hypotheses used here are staged and await source check.
The length and inverse-Weyl properties are not established here.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A finite Weyl scaling satisfies the triangle inequality after taking its
real representative. -/
theorem IsEuclideanLengthMetric.weylScaling_toReal_triangle
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (ξ : ℝ) (f : ℂ → ℝ)
    (hfinite : ∀ x y, weylScaling D ξ f x y ≠ ∞) (x y z : ℂ) :
    (weylScaling D ξ f x z).toReal ≤
      (weylScaling D ξ f x y).toReal + (weylScaling D ξ f y z).toReal := by
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinite x y, hfinite y z⟩)
    (hD.weylScaling_triangle ξ f x y z)
  rwa [ENNReal.toReal_add (hfinite x y) (hfinite y z)] at h

/-- For a logarithmically singular field, a continuous compactly supported
nonpositive Weyl bump yields a metric inducing the Euclidean topology almost
surely. This conclusion uses the staged metric-field axioms. -/
theorem ae_singularField_weylBump_metric_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      (∀ z, f z ≤ 0) →
      let E : ℂ → ℂ → ℝ := fun x y => (weylScaling (D ω) ξ f x y).toReal
      (∀ x, E x x = 0) ∧ (∀ x y, E x y = 0 → x = y) ∧
      (∀ x y, E x y = E y x) ∧ (∀ x y z, E x z ≤ E x y + E y z) ∧
      (∀ U : Set ℂ, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, E x y < ε → y ∈ U) := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD,
    ae_weylScaling_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD,
    ae_singularField_weylBump_symmetric_topology_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ] with ω hm hz ht
  intro f hf hc hu
  obtain ⟨hdiag, hsep, hsymm, htop⟩ := ht f hf hc hu
  obtain ⟨c, hl⟩ := exists_lower_bound_of_continuous_compactSupport f hf hc
  have hfinite : ∀ x y, weylScaling (D ω) ξ f x y ≠ ∞ := by
    intro x y
    exact (weylScaling_negative_bump_real_bounds hm hξ f hl hu hz x y).1.ne
  exact ⟨hdiag, hsep, hsymm, hm.weylScaling_toReal_triangle ξ f hfinite, htop⟩

end HarmonicBalls
